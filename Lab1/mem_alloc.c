// mem_alloc.c - General-purpose memory allocator with block headers (tags)

#define _GNU_SOURCE
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include <sys/mman.h>

/* ------------------------------ Alignment ------------------------------ */
#define ALIGN_SIZE (sizeof(void *) * 2)
#define ALIGN(x)   (((size_t)(x) + ALIGN_SIZE - 1) & ~(ALIGN_SIZE - 1))

/* ------------------- Flags (low 3 bits of size_flags) ------------------ */
#define FLAG_BUSY  ((size_t)1)
#define FLAG_FIRST ((size_t)2)
#define FLAG_LAST  ((size_t)4)
#define FLAG_MASK  ((size_t)7)

/* ----------------------------- Block header ---------------------------- */
typedef struct block_hdr {
    size_t size_flags;
    size_t prev_size;
} block_hdr_t;

#define HDR_SIZE  ALIGN(sizeof(block_hdr_t)) // 16 B

// AVL node is stored inside the free block's memory, MIN_BLOCK_SIZE must be large enough to fit it
typedef struct avl_node {
    struct avl_node *left, *right, *parent;
    int    height;
    size_t key;			// block size
    struct avl_node *same_next; // List of blocks with the same size
} avl_node_t;

// Minimum block size = header + space for avl_node_t
#define MIN_BLOCK_SIZE (HDR_SIZE + ALIGN(sizeof(avl_node_t)))

// Get block size (without flags)
static inline size_t blk_size (const block_hdr_t *b){ return b->size_flags & ~FLAG_MASK; }

// Check block flags
static inline int blk_busy (const block_hdr_t *b){ return !!(b->size_flags & FLAG_BUSY);  }
static inline int blk_first(const block_hdr_t *b){ return !!(b->size_flags & FLAG_FIRST); }
static inline int blk_last (const block_hdr_t *b){ return !!(b->size_flags & FLAG_LAST);  }

// Move between blocks
static inline block_hdr_t *blk_next(block_hdr_t *b){ return (block_hdr_t*)((char*)b + blk_size(b)); }
static inline block_hdr_t *blk_prev(block_hdr_t *b){ return (block_hdr_t*)((char*)b - b->prev_size); }

// Convert between block and user memory
static inline void *blk_usr(block_hdr_t *b){ return (char*)b + HDR_SIZE; }
static inline block_hdr_t *usr_blk(void *p){ return (block_hdr_t*)((char*)p - HDR_SIZE); }

// Set all block fields (size + flags + previous size)
static void blk_set(block_hdr_t *b, size_t sz, size_t psz, int busy, int first, int last)
{
    b->size_flags = sz
        | (busy  ? FLAG_BUSY  : 0)
        | (first ? FLAG_FIRST : 0)
        | (last  ? FLAG_LAST  : 0);
    b->prev_size = psz;
}

// previous block size = current block size
static void blk_sync_next(block_hdr_t *b){
    if(!blk_last(b)) blk_next(b)->prev_size = blk_size(b);
}

/* ----------------------------- Arena header ---------------------------- */
typedef struct arena_hdr {
    size_t total_size;
    int    is_large;
    struct arena_hdr *next, *prev;
} arena_hdr_t;

#define ARENA_HDR_SIZE  ALIGN(sizeof(arena_hdr_t))

static inline block_hdr_t *arena_first_blk(arena_hdr_t *a){
    return (block_hdr_t*)((char*)a + ARENA_HDR_SIZE);
}

/* ------------------------------- AVL tree ------------------------------ */
typedef struct { avl_node_t *root; } avl_tree_t;

static int avl_ht(avl_node_t *n){ return n ? n->height : 0; }

static void avl_upd(avl_node_t *n){
    int l = avl_ht(n->left), r = avl_ht(n->right);
    n->height = 1 + (l > r ? l : r);
}

// Replace old node with new node in parent
static void avl_repl(avl_tree_t *t, avl_node_t *par,
                     avl_node_t *old, avl_node_t *neo)
{
    if(!par) t->root = neo;
    else if(par->left==old) par->left = neo;
    else par->right = neo;
    if(neo) neo->parent = par;
}

static avl_node_t *avl_rot_l(avl_tree_t *t, avl_node_t *x){
    avl_node_t *y = x->right;
    avl_repl(t, x->parent, x, y);
    x->right = y->left; if(y->left) y->left->parent  = x;
    y->left  = x; x->parent = y;
    avl_upd(x); avl_upd(y);
    return y;
}
static avl_node_t *avl_rot_r(avl_tree_t *t, avl_node_t *x){
    avl_node_t *y = x->left;
    avl_repl(t, x->parent, x, y);
    x->left  = y->right; if(y->right) y->right->parent = x;
    y->right = x; x->parent = y;
    avl_upd(x); avl_upd(y);
    return y;
}

// Rebalance each node from n to root
static void avl_fix(avl_tree_t *t, avl_node_t *n){
    for(; n; n = n->parent){
        avl_upd(n);
        int bf = avl_ht(n->right) - avl_ht(n->left);
        if(bf > 1){
            if(avl_ht(n->right->right) < avl_ht(n->right->left))
                avl_rot_r(t, n->right);
            n = avl_rot_l(t, n);
        } else if(bf < -1){
            if(avl_ht(n->left->left) < avl_ht(n->left->right))
                avl_rot_l(t, n->left);
            n = avl_rot_r(t, n);
        }
    }
}

static void avl_insert(avl_tree_t *t, block_hdr_t *blk){
    avl_node_t *n = (avl_node_t*)blk_usr(blk);
    n->key = blk_size(blk);
    n->left = n->right = n->parent = NULL;
    n->height = 1;
    n->same_next = NULL;

    avl_node_t **cur = &t->root, *par = NULL;
    while(*cur){
        par = *cur;
        if(n->key == par->key){
            // Same size -> add to list
            n->same_next = par->same_next;
            par->same_next = n;
            return;
        }
        cur = (n->key < par->key) ? &par->left : &par->right;
    }
    *cur = n; n->parent = par;
    if(par) avl_fix(t, par);
}

static void avl_remove(avl_tree_t *t, block_hdr_t *blk){
    avl_node_t *n = (avl_node_t*)blk_usr(blk);

    // Find the tree node for this key
    avl_node_t *tn = t->root;
    while(tn && tn->key != n->key)
        tn = (n->key < tn->key) ? tn->left : tn->right;
    if(!tn) return;

    if(tn != n){
        /* If n is in the same-size linked list then unlink it */
        avl_node_t *p = tn;
        while(p->same_next && p->same_next != n) p = p->same_next;
        if(p->same_next == n) p->same_next = n->same_next;
        return;
    }

    // If there is a same-size node then replace n with it
    if(n->same_next){
        avl_node_t *peer = n->same_next;
        avl_repl(t, n->parent, n, peer);
        peer->left   = n->left;   if(peer->left)   peer->left->parent   = peer;
        peer->right  = n->right;  if(peer->right)  peer->right->parent  = peer;
        peer->height = n->height;
        return;
    }

    // Remove node from AVL tree
    avl_node_t *fix;
    if(!n->left || !n->right){
        avl_node_t *ch = n->left ? n->left : n->right;
        fix = n->parent;
        avl_repl(t, n->parent, n, ch);
    } else {
        // Node has 2 children -> find successor
        avl_node_t *s = n->right;
        while(s->left) s = s->left;
        fix = (s->parent == n) ? s : s->parent;
        avl_repl(t, s->parent, s, s->right);
        s->left  = n->left;  if(s->left)  s->left->parent  = s;
        s->right = n->right; if(s->right) s->right->parent = s;
        s->height = n->height;
        avl_repl(t, n->parent, n, s);
    }
    avl_fix(t, fix);
}

// Find smallest free block ≥ need
static block_hdr_t *avl_best(avl_tree_t *t, size_t need){
    avl_node_t *cur = t->root, *best = NULL;
    while(cur){
        if(cur->key >= need){ best = cur; cur = cur->left; }
        else                  cur = cur->right;
    }
    return best ? usr_blk((void*)best) : NULL;
}

/* ----------------------------- Global state ---------------------------- */
static size_t       g_page_size  = 0;
static size_t       g_arena_size = 0;
static arena_hdr_t *g_arenas     = NULL;
static avl_tree_t   g_free       = {NULL};

/* ------------------------------ OS helpers ----------------------------- */
static void *os_alloc(size_t sz){
    void *p = mmap(NULL, sz, PROT_READ|PROT_WRITE,
                   MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    return (p == MAP_FAILED) ? NULL : p;
}
static void os_free_mem(void *p, size_t sz){ munmap(p, sz); }
static void os_advise(void *p, size_t sz){
    if(!sz) return;
#ifdef MADV_FREE
    madvise(p, sz, MADV_FREE);
#elif defined(MADV_DONTNEED)
    madvise(p, sz, MADV_DONTNEED);
#endif
}
static size_t page_round(size_t n){
    if(!g_page_size) return n;
    return ((n + g_page_size - 1) / g_page_size) * g_page_size;
}

/* --------------------------- Arena management -------------------------- */
static arena_hdr_t *arena_new(size_t payload, int force_large){
    size_t need  = ARENA_HDR_SIZE + HDR_SIZE + ALIGN(payload);
    int    large = force_large || (need > g_arena_size);
    size_t sz    = large ? page_round(need) : g_arena_size;

    void *mem = os_alloc(sz);
    if(!mem) return NULL;

    arena_hdr_t *a = (arena_hdr_t*)mem;
    a->total_size  = sz;
    a->is_large    = large;
    a->next = g_arenas; a->prev = NULL;
    if(g_arenas) g_arenas->prev = a;
    g_arenas = a;

    // Initialize arena with a single free block filling it
    block_hdr_t *b = arena_first_blk(a);
    blk_set(b, sz - ARENA_HDR_SIZE, 0, 0, 1, 1);
    return a;
}

// Remove arena from global list and free its memory
static void arena_unlink(arena_hdr_t *a){
    if(a->prev) a->prev->next = a->next; else g_arenas = a->next;
    if(a->next) a->next->prev = a->prev;
    os_free_mem(a, a->total_size);
}

// Return the arena that contains block blk, or NULL
static arena_hdr_t *find_arena(block_hdr_t *blk){
    for(arena_hdr_t *c = g_arenas; c; c = c->next)
        if((char*)blk >= (char*)c && (char*)blk < (char*)c + c->total_size)
            return c;
    return NULL;
}

/* --------------------------- coalesce / split -------------------------- */
static block_hdr_t *coalesce(block_hdr_t *b){
    int    first = blk_first(b), last = blk_last(b);
    size_t sz    = blk_size(b), psz = b->prev_size;

    if(!last){
        block_hdr_t *nb = blk_next(b);
        if(!blk_busy(nb)){
            avl_remove(&g_free, nb);
            sz  += blk_size(nb);
            last = blk_last(nb);
        }
    }
    if(!first){
        block_hdr_t *pb = blk_prev(b);
        if(!blk_busy(pb)){
            avl_remove(&g_free, pb);
            psz   = pb->prev_size;
            sz   += blk_size(pb);
            first = blk_first(pb);
            b     = pb;
        }
    }
    blk_set(b, sz, psz, 0, first, last);
    blk_sync_next(b);
    return b;
}

static block_hdr_t *split_blk(block_hdr_t *b, size_t need){
    size_t total = blk_size(b), rem = total - need;
    int first = blk_first(b), last = blk_last(b);

    if(rem < MIN_BLOCK_SIZE){
        blk_set(b, total, b->prev_size, 1, first, last);
        blk_sync_next(b);
        return b;
    }
    blk_set(b, need, b->prev_size, 1, first, 0);

    block_hdr_t *r = blk_next(b);
    blk_set(r, rem, need, 0, 0, last);
    blk_sync_next(r);
    avl_insert(&g_free, r);
    return b;
}

/* ------------------------------ Public API ----------------------------- */
void mem_init(size_t page_size, size_t arena_size){
    g_page_size  = page_size;
    g_arena_size = arena_size;
    if(!g_arena_size)
        g_arena_size = page_size ? page_size * 16 : 65536;
    // must hold at least a few blocks
    size_t mn = ARENA_HDR_SIZE + MIN_BLOCK_SIZE * 4;
    if(g_arena_size < mn) g_arena_size = mn;
    g_arena_size = page_round(g_arena_size);
    g_arenas = NULL;
    g_free.root = NULL;
}

/* ------------------------------- mem_alloc ----------------------------- */
void *mem_alloc(size_t size){
    if(!size) return NULL;

    size_t need = HDR_SIZE + ALIGN(size);
    if(need < MIN_BLOCK_SIZE) need = MIN_BLOCK_SIZE;

    int large = (need > g_arena_size - ARENA_HDR_SIZE);

    if(!large){
        block_hdr_t *b = avl_best(&g_free, need);
        if(b){
            avl_remove(&g_free, b);
            return blk_usr(split_blk(b, need));
        }
    }

    arena_hdr_t *a = arena_new(size, large);
    if(!a) return NULL;

    block_hdr_t *b = arena_first_blk(a);
    if(large){
        blk_set(b, blk_size(b), 0, 1, 1, 1);
        return blk_usr(b);
    }
    avl_insert(&g_free, b);
    b = avl_best(&g_free, need);
    avl_remove(&g_free, b);
    return blk_usr(split_blk(b, need));
}

/* -------------------------------- mem_free ----------------------------- */
void mem_free(void *ptr){
    if(!ptr) return;

    block_hdr_t *blk = usr_blk(ptr);
    blk->size_flags &= ~FLAG_BUSY;

    arena_hdr_t *a = find_arena(blk);
    if(!a) return;

    if(a->is_large){
        arena_unlink(a);
        return;
    }

    blk = coalesce(blk);

    if(blk_first(blk) && blk_last(blk)){
        arena_unlink(a);
        return;
    }

    // Advise OS that pages holding only free data can be reclaimed
    if(g_page_size){
        uintptr_t s  = (uintptr_t)blk + HDR_SIZE;
        uintptr_t e  = (uintptr_t)blk + blk_size(blk);
        uintptr_t ps = (s + g_page_size - 1) & ~(g_page_size - 1);
        uintptr_t pe = e & ~(g_page_size - 1);
        if(pe > ps) os_advise((void*)ps, (size_t)(pe - ps));
    }

    avl_insert(&g_free, blk);
}

/* ------------------------------ mem_realloc ---------------------------- */
void *mem_realloc(void *ptr, size_t size){
    if(!ptr)  return mem_alloc(size);
    if(!size){ mem_free(ptr); return NULL; }

    block_hdr_t *blk   = usr_blk(ptr);
    size_t old_total   = blk_size(blk);
    size_t old_payload = old_total - HDR_SIZE;

    size_t need = HDR_SIZE + ALIGN(size);
    if(need < MIN_BLOCK_SIZE) need = MIN_BLOCK_SIZE;

    // in-place shrink
    if(need <= old_total){
        size_t rem = old_total - need;
        if(rem >= MIN_BLOCK_SIZE){
            int first = blk_first(blk), last = blk_last(blk);
            blk_set(blk, need, blk->prev_size, 1, first, 0);

            block_hdr_t *r = blk_next(blk);
            blk_set(r, rem, need, 0, 0, last);
            blk_sync_next(r);
            r = coalesce(r);
            avl_insert(&g_free, r);
        }
        return ptr;
    }

    // in-place grow (absorb following free block)
    if(!blk_last(blk)){
        block_hdr_t *nb = blk_next(blk);
        if(!blk_busy(nb) && old_total + blk_size(nb) >= need){
            avl_remove(&g_free, nb);
            size_t combined = old_total + blk_size(nb);
            int last = blk_last(nb);
            blk_set(blk, combined, blk->prev_size, 1, blk_first(blk), last);
            blk_sync_next(blk);

            size_t rem = combined - need;
            if(rem >= MIN_BLOCK_SIZE){
                blk_set(blk, need, blk->prev_size, 1, blk_first(blk), 0);
                block_hdr_t *r = blk_next(blk);
                blk_set(r, rem, need, 0, 0, last);
                blk_sync_next(r);
                avl_insert(&g_free, r);
            }
            return ptr;
        }
    }

    // allocate-copy-free
    void *np = mem_alloc(size);
    if(!np) return NULL;

    size_t copy = old_payload < ALIGN(size) ? old_payload : ALIGN(size);
    memcpy(np, ptr, copy);
    mem_free(ptr);
    return np;
}

/* ------------------------------- mem_show ------------------------------ */
void mem_show(void){
    printf("=== mem_show === page_size=%zu  arena_size=%zu\n",
           g_page_size, g_arena_size);
    int ai = 0;
    for(arena_hdr_t *a = g_arenas; a; a = a->next, ai++){
        printf("Arena[%d] @%p  total=%zu  %s\n",
               ai, (void*)a, a->total_size,
               a->is_large ? "[LARGE]" : "[default]");
        block_hdr_t *b = arena_first_blk(a);
        for(int bi = 0; ; bi++){
            printf("  blk[%d] @%p  sz=%6zu  psz=%6zu  [%s%s%s]\n",
                   bi, (void*)b, blk_size(b), b->prev_size,
                   blk_busy(b)  ? "BUSY"  : "free",
                   blk_first(b) ? " FIRST" : "",
                   blk_last(b)  ? " LAST"  : "");
            if(blk_last(b)) break;
            b = blk_next(b);
        }
    }
    printf("================\n");
}

/* --------------------------- Automated tester -------------------------- */
#define MAX_PTRS   256
#define ITERATIONS 5000

typedef unsigned char u8;

static u8 xsum(const u8 *p, size_t n){
    u8 s = 0; for(size_t i = 0; i < n; i++) s ^= p[i]; return s;
}

typedef struct { void *ptr; size_t sz; u8 csum; int used; } entry_t;
static entry_t tbl[MAX_PTRS];

static void fill(void *p, size_t n){
    u8 *b = (u8*)p; for(size_t i = 0; i < n; i++) b[i] = (u8)rand();
}

static void verify_all(void){
    for(int i = 0; i < MAX_PTRS; i++){
        if(!tbl[i].used) continue;
        u8 c = xsum(tbl[i].ptr, tbl[i].sz);
        if(c != tbl[i].csum){
            fprintf(stderr, "CHECKSUM MISMATCH at slot %d ptr=%p sz=%zu\n",
                    i, tbl[i].ptr, tbl[i].sz);
            assert(0);
        }
    }
}

static void test_run(void){
    srand((unsigned)time(NULL));
    memset(tbl, 0, sizeof(tbl));

    for(int it  = 0; it < ITERATIONS; it++){
        int op  = rand() % 3;
        int idx = rand() % MAX_PTRS;

        if(op == 0){
            if(tbl[idx].used) continue;
            size_t sz = (size_t)(rand() % 8192) + 1;
            void *p = mem_alloc(sz); if(!p) continue;
            fill(p, sz);
            tbl[idx] = (entry_t){p, sz, xsum(p, sz), 1};

        } else if(op == 1){
            if(!tbl[idx].used) continue;
            assert(xsum(tbl[idx].ptr, tbl[idx].sz) == tbl[idx].csum);
            mem_free(tbl[idx].ptr);
            tbl[idx].used = 0;

        } else {
            size_t nsz = (size_t)(rand() % 8192) + 1;
            if(tbl[idx].used){
                assert(xsum(tbl[idx].ptr, tbl[idx].sz) == tbl[idx].csum);
                void *np = mem_realloc(tbl[idx].ptr, nsz); if(!np) continue;
                fill(np, nsz);
                tbl[idx] = (entry_t){np, nsz, xsum(np, nsz), 1};
            } else {
                void *np = mem_alloc(nsz); if(!np) continue;
                fill(np, nsz);
                tbl[idx] = (entry_t){np, nsz, xsum(np, nsz), 1};
            }
        }
        if(it % 500 == 0) verify_all();
    }

    verify_all();
    // Free everything remaining
    for(int i = 0; i < MAX_PTRS; i++){
        if(!tbl[i].used) continue;
        assert(xsum(tbl[i].ptr, tbl[i].sz) == tbl[i].csum);
        mem_free(tbl[i].ptr);
    }
    printf("Automated test PASSED  (%d iterations)\n", ITERATIONS);
}

/* ---------------------------------- main-------------------------------- */
int main(void){
    mem_init(4096, 65536);

    printf("--- allocate 3 blocks ---\n");
    void *a = mem_alloc(100);
    void *b = mem_alloc(200);
    void *c = mem_alloc(50);
    mem_show();

    printf("--- free middle block (b) ---\n");
    mem_free(b);
    mem_show();

    printf("--- realloc a: 100 -> 400 bytes (grows in-place) ---\n");
    a = mem_realloc(a, 400);
    mem_show();

    printf("--- free a and c -> arena should be returned to OS ---\n");
    mem_free(a);
    mem_free(c);
    mem_show();

    printf("--- large allocation (2 MiB) ---\n");
    void *big = mem_alloc(2 * 1024 * 1024);
    mem_show();
    mem_free(big);
    mem_show();

    printf("\n--- Automated tester (%d iterations) ---\n", ITERATIONS);
    test_run();
    return 0;
}
