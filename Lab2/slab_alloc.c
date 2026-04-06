/* Лабораторна робота №2
 * slab_alloc.c - Алокатор пам'яті загального призначення з розподілом slab
 *
 * API: mem_init, mem_alloc, mem_free, mem_realloc, mem_show
 *
 * Архітектура:
 * 36 size-класів (16 ... 16384 байт) --> slab-алокація
 * Більші розміри --> extent з арени або прямий mmap
 * Radix tree (4 рівні, 9 біт кожен) --> O(1) пошук на free
 * Бітова карта арени --> best-fit пошук вільних сторінок
 * 
 */

#define _GNU_SOURCE
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include <sys/mman.h>


/* ================================================================
 *                           Налаштування                          
 * ================================================================ */
#define ALIGN_SIZE      16u   /* максимальне вирівнювання = sizeof(void*)*2 на 64-біт */
#define N_DIRECT        8u    /* перші N розмірів: крок = ALIGN_SIZE */
#define M_PER_GROUP     4u    /* розмірів у групі */
#define K_GROUPS        7u    /* кількість груп */
#define NUM_SC          (N_DIRECT + K_GROUPS * M_PER_GROUP)

#define MIN_SLAB_OBJS   1u    /* мінімум об'єктів у slab */
#define MAX_SLAB_PAGES  128u  /* максимум сторінок у slab */
#define MAX_ARENA_PAGES 4096u /* бітова карта арени (максимум) */

#define ALIGN_UP(x, a)  (((size_t)(x) + (a) - 1) & ~(size_t)((a) - 1))


/* ================================================================
 *                          Глобальний стан                        
 * ================================================================ */
static size_t   g_page_size  = 4096;
static size_t   g_arena_size = 0;
static unsigned g_page_shift = 12;    /* log2(page_size) */
static size_t   sc_sizes[NUM_SC];     /* розміри об'єктів size-класів */


/* ================================================================
 *          Допоміжні функції OS  (mmap / munmap / madvise)        
 * ================================================================ */
static void *os_alloc(size_t sz) {
    void *p = mmap(NULL, sz, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    return (p == MAP_FAILED) ? NULL : p;
}
static void os_free_mem(void *p, size_t sz) { munmap(p, sz); }
static void os_advise_free(void *p, size_t sz) {
    if (!sz) return;
#ifdef MADV_FREE
    madvise(p, sz, MADV_FREE);
#elif defined(MADV_DONTNEED)
    madvise(p, sz, MADV_DONTNEED);
#endif
}

/* Найбільший спільний дільник */
static size_t gcd_sz(size_t a, size_t b) {
    while (b) { size_t t = b; b = a % b; a = t; }
    return a;
}


/* ================================================================
 * Таблиця size-класів
 *
 * Перші 8: 16, 32, 48, 64, 80, 96, 112, 128
 * Група 1 (крок=32):  160, 192, 224, 256
 * Група 2 (крок=64):  320, 384, 448, 512
 * Група 3 (крок=128): 640, 768, 896, 1024
 * Група 4 (крок=256): 1280, 1536, 1792, 2048
 * Група 5 (крок=512): 2560, 3072, 3584, 4096
 * Група 6 (крок=1K):  5120, 6144, 7168, 8192
 * Група 7 (крок=2K):  10240, 12288, 14336, 16384
 * ================================================================ */
static void sc_init(void) {
    for (unsigned i = 0; i < N_DIRECT; i++)
        sc_sizes[i] = (size_t)(i + 1) * ALIGN_SIZE;

    size_t base = sc_sizes[N_DIRECT - 1];
    unsigned idx = N_DIRECT;
    for (unsigned p = 1; p <= K_GROUPS; p++) {
        size_t step = ((size_t)1 << p) * ALIGN_SIZE;
        for (unsigned j = 0; j < M_PER_GROUP; j++)
            sc_sizes[idx++] = base + (size_t)(j + 1) * step;
        base = sc_sizes[idx - 1];
    }
}

/*
 * Конвертація розміру --> індекс size-класу.
 * Повертає NUM_SC якщо розмір не вміщується в жоден slab-клас.
 *
 * Алгоритм з файлу завдання: знаходимо групу p через 
 * bit_length, потім номер всередині групи через формулу.
 */
static unsigned sc_index(size_t size) {
    if (!size) size = 1;

    /* Перші N_DIRECT класи: ceil(size/ALIGN) – 1 */
    if (size <= sc_sizes[N_DIRECT - 1])
        return (unsigned)((size + ALIGN_SIZE - 1) / ALIGN_SIZE) - 1;

    if (size > sc_sizes[NUM_SC - 1]) return NUM_SC; /* занадто великий */

    size_t sizen     = sc_sizes[N_DIRECT - 1];               /* 128 */
    size_t step_base = (size_t)M_PER_GROUP * ALIGN_SIZE * 2; /* 128 */

    /* lhs = floor((size – sizen – 1) / step_base) + 1 */
    size_t lhs = (size - sizen - 1) / step_base + 1;

    /* p = bit_length(lhs): найменше p таке що 2^p > lhs */
    unsigned p = 0;
    for (size_t tmp = lhs; tmp; tmp >>= 1) p++;
    if (p < 1) p = 1;
    if (p > K_GROUPS) p = K_GROUPS;

    size_t group_max = sizen + step_base * (((size_t)1 << p) - 1);
    size_t step      = ((size_t)1 << p) * ALIGN_SIZE;
    unsigned in_g    = M_PER_GROUP - (unsigned)((group_max - size) / step);
    if (!in_g) in_g  = 1;

    unsigned sc = N_DIRECT + (p - 1) * M_PER_GROUP + (in_g - 1);
    if (sc >= NUM_SC) sc = NUM_SC - 1;
    return sc;
}


/* ================================================================
 * Radix tree (4 рівні × 9 біт = 36 біт номера сторінки)
 *
 * Відображення: адреса сторінки --> покажчик на slab_hdr_t або
 *               (base_large_extent | 1) для великих алокацій.
 *
 * Тегування (bit 0 покажчика):
 * 0 --> slab_hdr_t * (slab-об'єкт)
 * 1 --> base великого extent
 * ================================================================ */
#define RTREE_LEVELS 4
#define RTREE_BITS   9
#define RTREE_SZ     (1 << RTREE_BITS) /* 512 */

typedef struct rtree_node { void *child[RTREE_SZ]; } rtree_node_t;

static rtree_node_t *g_rtree_root = NULL;

static rtree_node_t *rtree_alloc_node(void) {
    rtree_node_t *n = (rtree_node_t *)os_alloc(sizeof(rtree_node_t));
    if (n) memset(n, 0, sizeof(rtree_node_t));
    return n;
}

/* Отримати покажчик за адресою сторінки */
static void *rtree_get(void *ptr) {
    uintptr_t pn = (uintptr_t)ptr >> g_page_shift;
    if (!g_rtree_root) return NULL;
    rtree_node_t *node = g_rtree_root;
    for (int lv = 0; lv < RTREE_LEVELS - 1; lv++) {
        unsigned idx = (unsigned)((pn >> ((RTREE_LEVELS - 1 - lv) * RTREE_BITS))
                                  & (RTREE_SZ - 1));
        if (!node->child[idx]) return NULL;
        node = (rtree_node_t *)node->child[idx];
    }
    return node->child[pn & (RTREE_SZ - 1)];
}

/* Записати покажчик val для адреси сторінки ptr */
static int rtree_set(void *ptr, void *val) {
    uintptr_t pn = (uintptr_t)ptr >> g_page_shift;
    if (!g_rtree_root) {
        g_rtree_root = rtree_alloc_node();
        if (!g_rtree_root) return 0;
    }
    rtree_node_t *node = g_rtree_root;
    for (int lv = 0; lv < RTREE_LEVELS - 1; lv++) {
        unsigned idx = (unsigned)((pn >> ((RTREE_LEVELS - 1 - lv) * RTREE_BITS))
                                  & (RTREE_SZ - 1));
        if (!node->child[idx]) {
            node->child[idx] = rtree_alloc_node();
            if (!node->child[idx]) return 0;
        }
        node = (rtree_node_t *)node->child[idx];
    }
    node->child[pn & (RTREE_SZ - 1)] = val;
    return 1;
}

/* Встановити val для діапазону сторінок [base, base + n_pages) */
static void rtree_set_range(void *base, size_t n_pages, void *val) {
    char *p = (char *)base;
    for (size_t i = 0; i < n_pages; i++, p += g_page_size)
        rtree_set(p, val);
}


/* ================================================================
 *                               Arena                             
 *
 * Арена - великий mmap-регіон розміром g_arena_size.
 * Перша сторінка містить arena_hdr_t.
 * Решта сторінок - "керовані" сторінки для extent/slab.
 *
 * page_bmap: біт 1 = сторінка вільна.
 * ================================================================ */
typedef struct arena_hdr {
    struct arena_hdr *next, *prev;
    void   *base;      /* початок mmap (вирівняний на arena_size) */
    size_t  n_managed; /* кількість керованих сторінок */
    size_t  n_free;    /* кількість вільних сторінок */
    
    /* бітова карта: до MAX_ARENA_PAGES біт */
    uint64_t bmap[MAX_ARENA_PAGES / 64]; /* 64 слова × 8 = 512 байт */
} arena_hdr_t;

static arena_hdr_t *g_arenas = NULL;

static void arena_link(arena_hdr_t *a) {
    a->next = g_arenas; a->prev = NULL;
    if (g_arenas) g_arenas->prev = a;
    g_arenas = a;
}

static void arena_unlink(arena_hdr_t *a) {
    if (a->prev) a->prev->next = a->next; else g_arenas = a->next;
    if (a->next) a->next->prev = a->prev;
}

/* Позначити сторінки (start, start+count) у бітовій карті */
static void arena_bmap_set(arena_hdr_t *a, size_t start, size_t count, int free_flag) {
    for (size_t i = start; i < start + count; i++) {
        uint64_t *w = &a->bmap[i / 64];
        uint64_t  b = (uint64_t)1 << (i % 64);
        if (free_flag) *w |= b; else *w &= ~b;
    }
}

/*
 * Best-fit пошук: знайти найменший вільний run довжиною >= n.
 * Повертає початковий індекс або (size_t)-1.
 */
static size_t arena_find_run(arena_hdr_t *a, size_t n) {
    size_t best = (size_t)-1, best_len = (size_t)-1;
    size_t rs = 0, rl = 0;
    for (size_t i = 0; i <= a->n_managed; i++) {
        int free_pg = (i < a->n_managed) &&
                      ((a->bmap[i / 64] >> (i % 64)) & 1);
        if (free_pg) {
            if (!rl) rs = i;
            rl++;
        } else {
            if (rl >= n) {
                if (best_len == (size_t)-1 || rl < best_len) {
                    best = rs; best_len = rl;
                    if (rl == n) return best; /* best */
                }
            }
            rl = 0;
        }
    }
    return best;
}

/* Повернути вказівник на керовану сторінку i арени a */
static void *arena_page_ptr(arena_hdr_t *a, size_t i) {
    return (char *)a->base + (i + 1) * g_page_size;
}

/* Виділити extent з n_pages з будь-якої арени. out_arena – ідентифікатор арени. */
static void *arena_alloc_extent(size_t n_pages, arena_hdr_t **out_arena) {
    for (arena_hdr_t *a = g_arenas; a; a = a->next) {
        if (a->n_free < n_pages) continue;
        size_t si = arena_find_run(a, n_pages);
        if (si == (size_t)-1) continue;
        arena_bmap_set(a, si, n_pages, 0);
        a->n_free -= n_pages;
        *out_arena = a;
        return arena_page_ptr(a, si);
    }
    return NULL;
}

/* Створити нову арену */
static arena_hdr_t *arena_new(void) {
    void *mem = os_alloc(g_arena_size);
    if (!mem) return NULL;
    arena_hdr_t *a = (arena_hdr_t *)mem;
    memset(a, 0, sizeof(*a));
    a->base = mem;
    a->n_managed = g_arena_size / g_page_size - 1;
    if (a->n_managed > MAX_ARENA_PAGES) a->n_managed = MAX_ARENA_PAGES;
    a->n_free = a->n_managed;
    arena_bmap_set(a, 0, a->n_managed, 1);
    arena_link(a);
    return a;
}

/* Повернути extent з n_pages назад у арену */
static void arena_free_extent(arena_hdr_t *a, void *base, size_t n_pages) {
    /* Індекс керованої сторінки */
    size_t off = (size_t)((char *)base - (char *)a->base) / g_page_size - 1;
    arena_bmap_set(a, off, n_pages, 1);
    a->n_free += n_pages;
    os_advise_free(base, n_pages * g_page_size);
    
    /* Якщо арена повністю порожня -> повернути ядру */
    if (a->n_free == a->n_managed) {
        arena_unlink(a);
        os_free_mem(a->base, g_arena_size);
    }
}


/* ================================================================
 *     Extent header (для великих алокацій > sc_sizes[NUM_SC-1])   
 *
 * Зберігається на початку mmap-регіону.
 * Вказівник користувача = base + LARGE_HDR_SIZE.
 * У radix tree: rtree[base] = (base | 1)  (bit0=1 = велика алокація).
 * ================================================================ */
typedef struct extent_hdr {
    arena_hdr_t *arena;
    size_t n_pages;
} extent_hdr_t;

#define LARGE_HDR_SIZE  ALIGN_UP(sizeof(extent_hdr_t), ALIGN_SIZE)   /* 16 байт */


/* ================================================================
 *                            Slab header                          
 *
 * Зберігається на початку slab-extent (завжди вирівняна на сторінку).
 * Далі у тій самій пам'яті йде бітова карта, потім - об'єкти.
 *
 * [slab_hdr_t | bitmap uint64_t[] | padding | obj0 | obj1 | ...]
 *
 * Бітова карта: біт 1 = об'єкт вільний, біт 0 = зайнятий.
 * ================================================================ */
typedef struct slab_hdr {
    struct slab_hdr *next, *prev;  /* двозв'язаний список у кеші */
    void        *base;             /* початок slab-extent */
    arena_hdr_t *arena;            /* з якої арени */
    uint32_t     sc;               /* індекс size-класу */
    uint32_t     n_pages;          /* сторінок у slab */
    uint32_t     total_objs;       /* всього об'єктів */
    uint32_t     free_cnt;         /* вільних об'єктів */
    uint32_t     bmap_words;       /* слів у бітовій карті */
    uint32_t     obj_offset;       /* зміщення першого об'єкта від base */
} slab_hdr_t;

/* sizeof(slab_hdr_t) = 2×8 + 8 + 8 + 6×4 = 56 байт */

/* Бітова карта знаходиться одразу після slab_hdr_t у пам'яті */
static inline uint64_t *slab_bmap(slab_hdr_t *s) {
    return (uint64_t *)((char *)s + sizeof(slab_hdr_t));
}

/* Кеш slab: per-size-class список slab-ів із вільними об'єктами */
static slab_hdr_t *g_slab_cache[NUM_SC];

static void slab_cache_add(slab_hdr_t *s) {
    s->next = g_slab_cache[s->sc]; s->prev = NULL;
    if (g_slab_cache[s->sc]) g_slab_cache[s->sc]->prev = s;
    g_slab_cache[s->sc] = s;
}
static void slab_cache_remove(slab_hdr_t *s) {
    if (s->prev) s->prev->next = s->next;
    else         g_slab_cache[s->sc] = s->next;
    if (s->next) s->next->prev = s->prev;
    s->next = s->prev = NULL;
}

/* Обчислити мінімальну кількість сторінок для slab size-класу sc */
static size_t slab_compute_pages(unsigned sc) {
    size_t obj_size = sc_sizes[sc];
    size_t g        = gcd_sz(obj_size, g_page_size);
    size_t n_pages  = obj_size / g;   /* мінімум за формулою ymin */

    for (;;) {
        if (n_pages > MAX_SLAB_PAGES) return MAX_SLAB_PAGES;
        size_t slab_sz = n_pages * g_page_size;

        /* Груба оцінка кількості об'єктів для розрахунку розміру карти */
        size_t rough_n = slab_sz / obj_size;
        if (!rough_n) rough_n = 1;
        size_t bmap_w  = (rough_n + 63) / 64;
        size_t hdr_sz  = ALIGN_UP(sizeof(slab_hdr_t) + bmap_w * 8, ALIGN_SIZE);

        if (slab_sz <= hdr_sz) { n_pages++; continue; }
        size_t avail  = slab_sz - hdr_sz;
        size_t n_objs = avail / obj_size;
        if (n_objs >= MIN_SLAB_OBJS) return n_pages;
        n_pages++;
    }
}

/* Ініціалізувати slab_hdr_t у пам'яті base для size-класу sc */
static void slab_init(slab_hdr_t *s, void *base, arena_hdr_t *arena,
                      unsigned sc, size_t n_pages) {
    size_t obj_size = sc_sizes[sc];
    /* Ітераційно уточнюємо layout (через зворотній зв'язок розміру bitmap) */
    uint32_t total_objs = 0, bmap_words = 1;
    size_t   obj_offset = 0;
    for (int it = 0; it < 4; it++) {
        size_t hdr_sz  = ALIGN_UP(sizeof(slab_hdr_t) + (size_t)bmap_words * 8, ALIGN_SIZE);
        size_t slab_sz = n_pages * g_page_size;
        size_t avail   = (slab_sz > hdr_sz) ? slab_sz - hdr_sz : 0;
        total_objs = (uint32_t)(avail / obj_size);
        bmap_words = (total_objs + 63) / 64;
        if (!bmap_words) bmap_words = 1;
        obj_offset = (uint32_t)ALIGN_UP(sizeof(slab_hdr_t) + (size_t)bmap_words * 8,
                                        ALIGN_SIZE);
    }

    s->next = s->prev = NULL;
    s->base       = base;
    s->arena      = arena;
    s->sc         = sc;
    s->n_pages    = (uint32_t)n_pages;
    s->total_objs = total_objs;
    s->free_cnt   = total_objs;
    s->bmap_words = bmap_words;
    s->obj_offset = obj_offset;

    /* Позначити всі об'єкти вільними (біт = 1) */
    uint64_t *bm = slab_bmap(s);
    uint32_t full_words = total_objs / 64;
    uint32_t rem_bits   = total_objs % 64;
    for (uint32_t i = 0; i < full_words; i++) bm[i] = ~(uint64_t)0;
    if (rem_bits)
        bm[full_words] = ((uint64_t)1 << rem_bits) - 1;
        
    /* Залишок до bmap_words - нулі */
    for (uint32_t i = (rem_bits ? full_words + 1 : full_words);
         i < bmap_words; i++) bm[i] = 0;
}

/* Знайти перший вільний об'єкт у slab */
static uint32_t slab_find_free(slab_hdr_t *s) {
    uint64_t *bm = slab_bmap(s);
    for (uint32_t w = 0; w < s->bmap_words; w++) {
        if (!bm[w]) continue;
        uint32_t bit = (uint32_t)__builtin_ctzll(bm[w]);
        uint32_t idx = w * 64 + bit;
        if (idx < s->total_objs) return idx;
    }
    return (uint32_t)-1;
}

static inline void *slab_obj_ptr(slab_hdr_t *s, uint32_t idx) {
    return (char *)s->base + s->obj_offset + (size_t)idx * sc_sizes[s->sc];
}
static inline uint32_t slab_obj_idx(slab_hdr_t *s, void *ptr) {
    return (uint32_t)(((char *)ptr - ((char *)s->base + s->obj_offset))
                      / sc_sizes[s->sc]);
}

/* Взяти об'єкт зі slab */
static void *slab_take_obj(slab_hdr_t *s) {
    uint32_t idx = slab_find_free(s);
    if (idx == (uint32_t)-1) return NULL;
    uint64_t *bm = slab_bmap(s);
    bm[idx / 64] &= ~((uint64_t)1 << (idx % 64));  /* зайнятий */
    s->free_cnt--;
    return slab_obj_ptr(s, idx);
}

/* Повернути об'єкт у slab */
static void slab_return_obj(slab_hdr_t *s, void *ptr) {
    uint32_t idx = slab_obj_idx(s, ptr);
    uint64_t *bm = slab_bmap(s);
    bm[idx / 64] |= ((uint64_t)1 << (idx % 64));   /* вільний */
    s->free_cnt++;
}

/* Створити новий slab для size-класу sc */
static slab_hdr_t *slab_new(unsigned sc) {
    size_t       n_pages = slab_compute_pages(sc);
    arena_hdr_t *arena   = NULL;
    void        *base    = NULL;

    /* Шукаємо місце в існуючих аренах */
    base = arena_alloc_extent(n_pages, &arena);
    if (!base) {
        /* Потрібна нова арена */
        if (!arena_new()) return NULL;
        base = arena_alloc_extent(n_pages, &arena);
        if (!base) return NULL;
    }

    slab_hdr_t *s = (slab_hdr_t *)base;
    slab_init(s, base, arena, sc, n_pages);

    /* Реєструємо кожну сторінку slab у radix tree --> slab_hdr* (bit0=0) */
    rtree_set_range(base, n_pages, s);

    slab_cache_add(s);
    return s;
}

/* Знищити slab: очистити radix tree і повернути extent у арену */
static void slab_destroy(slab_hdr_t *s) {
    void        *base    = s->base;
    size_t       n_pages = s->n_pages;
    arena_hdr_t *arena   = s->arena;
    
    /* Спочатку очищаємо radix tree (поки s ще доступний) */
    rtree_set_range(base, n_pages, NULL);
    
    /* Повертаємо пам'ять у арену (може звільнити арену --> munmap) */
    arena_free_extent(arena, base, n_pages);
}


/* ================================================================
 *                                API                              
 * ================================================================ */

void mem_init(size_t page_size, size_t arena_size) {
    g_page_size  = page_size  ? page_size  : 4096;
    g_arena_size = arena_size ? arena_size : g_page_size * 256;

    /* Обчислити log2(page_size) */
    g_page_shift = 0;
    for (size_t ps = g_page_size; ps > 1; ps >>= 1) g_page_shift++;

    sc_init();
    memset(g_slab_cache, 0, sizeof(g_slab_cache));
    g_arenas     = NULL;
    g_rtree_root = NULL;
}


/* ================================================================
 *                            mem_alloc                            
 * ================================================================ */
void *mem_alloc(size_t size) {
    if (!size) return NULL;

    unsigned sc = sc_index(size);

    /* Slab-алокація (36 size-класів) */
    if (sc < NUM_SC) {
        slab_hdr_t *s = g_slab_cache[sc];
        if (!s) {
            s = slab_new(sc);
            if (!s) return NULL;
        }
        void *ptr = slab_take_obj(s);
        
        /* Якщо slab заповнився - прибрати з кешу */
        if (s->free_cnt == 0) slab_cache_remove(s);
        return ptr;
    }

    /*  Велика алокація: extent  */
    size_t n_pages = (size + LARGE_HDR_SIZE + g_page_size - 1) / g_page_size;
    void        *base  = NULL;
    arena_hdr_t *arena = NULL;

    /* Спробувати отримати extent з арени */
    if (n_pages < g_arena_size / g_page_size - 1) {
        base = arena_alloc_extent(n_pages, &arena);
        if (!base) {
            if (arena_new()) base = arena_alloc_extent(n_pages, &arena);
        }
    }

    if (!base) {
        /* Прямий mmap */
        base = os_alloc(n_pages * g_page_size);
        if (!base) return NULL;
        arena = NULL;
    }

    /* Записати extent header у початок extent */
    extent_hdr_t *eh = (extent_hdr_t *)base;
    eh->arena   = arena;
    eh->n_pages = n_pages;

    /* Реєстрація у radix tree: base | 1 (bit0=1 = велика алокація) */
    rtree_set(base, (void *)((uintptr_t)base | 1u));

    return (char *)base + LARGE_HDR_SIZE;
}


/* ================================================================
 *                             mem_free                            
 * ================================================================ */
void mem_free(void *ptr) {
    if (!ptr) return;

    /* Знайти сторінку і отримати запис з radix tree */
    void *page_start = (void *)((uintptr_t)ptr & ~(g_page_size - 1));
    void *rtval      = rtree_get(page_start);
    if (!rtval) return;   /* неправильний покажчик або помилка */

    if ((uintptr_t)rtval & 1u) {
        /* Велика алокація */
        void *base = (void *)((uintptr_t)rtval & ~(uintptr_t)1u);
        extent_hdr_t *eh = (extent_hdr_t *)base;
        size_t       n_pages = eh->n_pages;
        arena_hdr_t *arena   = eh->arena;

        rtree_set(base, NULL);   /* прибрати з radix tree */

        if (arena) {
            arena_free_extent(arena, base, n_pages);
        } else {
            os_free_mem(base, n_pages * g_page_size);
        }
    } else {
        /* Slab-об'єкт */
        slab_hdr_t *s       = (slab_hdr_t *)rtval;
        int         was_full = (s->free_cnt == 0);

        slab_return_obj(s, ptr);

        /* Якщо slab був повністю зайнятий - повернути у кеш */
        if (was_full) slab_cache_add(s);

        /* Якщо slab повністю порожній - повернути extent у арену */
        if (s->free_cnt == s->total_objs) {
            slab_cache_remove(s);
            slab_destroy(s);
        } else {
            /* Повідомити ОС про вільні сторінки всередині slab
             * (спрощений варіант: madvise на весь user-area якщо >75% вільних) */
            if (s->free_cnt * 4 >= s->total_objs * 3) {
                char *obj_area = (char *)s->base + s->obj_offset;
                size_t obj_area_sz = s->total_objs * sc_sizes[s->sc];
                
                /* Вирівняти до сторінки */
                uintptr_t ps = ALIGN_UP((uintptr_t)obj_area, g_page_size);
                uintptr_t pe = (uintptr_t)(obj_area + obj_area_sz) & ~(g_page_size - 1);
                if (pe > ps) os_advise_free((void *)ps, pe - ps);
            }
        }
    }
}


/* ================================================================
 *                            mem_realloc                          
 * ================================================================ */
void *mem_realloc(void *ptr, size_t size) {
    if (!ptr)  return mem_alloc(size);
    if (!size) { mem_free(ptr); return NULL; }

    /* Визначити поточний доступний розмір */
    void *page_start = (void *)((uintptr_t)ptr & ~(g_page_size - 1));
    void *rtval      = rtree_get(page_start);
    if (!rtval) return NULL;

    size_t current_usable;
    if ((uintptr_t)rtval & 1u) {
        /* Велика алокація */
        void         *base = (void *)((uintptr_t)rtval & ~(uintptr_t)1u);
        extent_hdr_t *eh   = (extent_hdr_t *)base;
        current_usable     = eh->n_pages * g_page_size - LARGE_HDR_SIZE;
    } else {
        /* Slab-об'єкт */
        slab_hdr_t *s  = (slab_hdr_t *)rtval;
        current_usable = sc_sizes[s->sc];
    }

    /* In-place якщо новий розмір вміщується у поточну алокацію */
    if (size <= current_usable) return ptr;

    /* Спроба in-place зростання для великого extent:
     * якщо новий розмір вміститься в існуючі сторінки (запас округлення) */
    if ((uintptr_t)rtval & 1u) {
        void         *base     = (void *)((uintptr_t)rtval & ~(uintptr_t)1u);
        extent_hdr_t *eh       = (extent_hdr_t *)base;
        size_t        n_needed = (size + LARGE_HDR_SIZE + g_page_size - 1) / g_page_size;
        if (n_needed <= eh->n_pages) return ptr;
    }

    /* Allocate – copy – free */
    void *np = mem_alloc(size);
    if (!np) return NULL;
    size_t copy = (current_usable < size) ? current_usable : size;
    memcpy(np, ptr, copy);
    mem_free(ptr);
    return np;
}


/* ================================================================
 *                             mem_show                            
 * ================================================================ */
void mem_show(void) {
    printf("\n======================== mem_show ========================\n");
    printf("  page_size  = %zu  arena_size = %zu\n", g_page_size, g_arena_size);
    printf("  LARGE_HDR  = %zu  NUM_SC = %u\n", LARGE_HDR_SIZE, NUM_SC);

    /* Таблиця size-класів */
    printf("\n  Size classes (%u total):\n", NUM_SC);
    printf("  ");
    for (unsigned i = 0; i < NUM_SC; i++) {
        printf("[%u]=%zu ", i, sc_sizes[i]);
        if ((i + 1) % 8 == 0) printf("\n  ");
    }
    printf("\n");

    /* Арени */
    int ai = 0;
    printf("\n  Arenas:\n");
    for (arena_hdr_t *a = g_arenas; a; a = a->next, ai++) {
        printf("    Arena[%d] base=%p  managed=%zu  free=%zu  used=%zu\n",
               ai, a->base, a->n_managed, a->n_free, a->n_managed - a->n_free);
    }
    if (!g_arenas) printf("    (немає)\n");

    /* Slab кеші */
    printf("\n  Slab caches (тільки ті що мають вільні slab-и):\n");
    int any = 0;
    for (unsigned sc = 0; sc < NUM_SC; sc++) {
        if (!g_slab_cache[sc]) continue;
        any = 1;
        printf("    SC[%u] obj_size=%-6zu  slabs:\n", sc, sc_sizes[sc]);
        for (slab_hdr_t *s = g_slab_cache[sc]; s; s = s->next) {
            printf("      Slab @%p  pages=%u  total=%u  free=%u  busy=%u\n",
                   s->base, s->n_pages, s->total_objs, s->free_cnt,
                   s->total_objs - s->free_cnt);
        }
    }
    if (!any) printf("    (усі slab-и або повні, або повернуті арені)\n");

    printf("==========================================================\n\n");
}


/* ================================================================
 *                        Автоматичний тестер                      
 * ================================================================ */
#define MAX_PTRS   256
#define ITERATIONS 5000

typedef unsigned char u8;

static u8 xsum(const u8 *p, size_t n) {
    u8 s = 0;
    for (size_t i = 0; i < n; i++) s ^= p[i];
    return s;
}

typedef struct { void *ptr; size_t sz; u8 csum; int used; } entry_t;
static entry_t tbl[MAX_PTRS];

static void fill(void *p, size_t n) {
    u8 *b = (u8 *)p;
    for (size_t i = 0; i < n; i++) b[i] = (u8)rand();
}
static void verify_all(void) {
    for (int i = 0; i < MAX_PTRS; i++) {
        if (!tbl[i].used) continue;
        u8 c = xsum(tbl[i].ptr, tbl[i].sz);
        if (c != tbl[i].csum) {
            fprintf(stderr, "CHECKSUM MISMATCH slot=%d ptr=%p sz=%zu\n",
                    i, tbl[i].ptr, tbl[i].sz);
            assert(0);
        }
    }
}

static void test_run(void) {
    srand((unsigned)time(NULL));
    memset(tbl, 0, sizeof(tbl));
    for (int it = 0; it < ITERATIONS; it++) {
        int op  = rand() % 3;
        int idx = rand() % MAX_PTRS;

        if (op == 0) {
            if (tbl[idx].used) continue;
            size_t sz = (size_t)(rand() % 8192) + 1;
            void *p = mem_alloc(sz);
            if (!p) continue;
            fill(p, sz);
            tbl[idx] = (entry_t){p, sz, xsum(p, sz), 1};

        } else if (op == 1) {
            if (!tbl[idx].used) continue;
            assert(xsum(tbl[idx].ptr, tbl[idx].sz) == tbl[idx].csum);
            mem_free(tbl[idx].ptr);
            tbl[idx].used = 0;

        } else {
            size_t nsz = (size_t)(rand() % 8192) + 1;
            if (tbl[idx].used) {
                assert(xsum(tbl[idx].ptr, tbl[idx].sz) == tbl[idx].csum);
                void *np = mem_realloc(tbl[idx].ptr, nsz);
                if (!np) continue;
                fill(np, nsz);
                tbl[idx] = (entry_t){np, nsz, xsum(np, nsz), 1};
            } else {
                void *np = mem_alloc(nsz);
                if (!np) continue;
                fill(np, nsz);
                tbl[idx] = (entry_t){np, nsz, xsum(np, nsz), 1};
            }
        }
        if (it % 500 == 0) verify_all();
    }
    verify_all();
    for (int i = 0; i < MAX_PTRS; i++) {
        if (!tbl[i].used) continue;
        assert(xsum(tbl[i].ptr, tbl[i].sz) == tbl[i].csum);
        mem_free(tbl[i].ptr);
    }
    printf("Automated test PASSED (%d iterations)\n", ITERATIONS);
}

/* ================================================================
 *                               main                              
 * ================================================================ */
int main(void) {
    printf("========== Slab Allocator - Lab 2 ==========\n");
    mem_init(4096, 4096 * 64);   /* сторінка 4 КБ, арена 256 КБ */

    /* --- Базова демонстрація --- */
    printf("\n--- Виділяємо 3 блоки різних розмірів ---\n");
    void *a = mem_alloc(100);   /* --> SC[6]=112 байт */
    void *b = mem_alloc(500);   /* --> SC[15]=512 байт */
    void *c = mem_alloc(40);    /* --> SC[2]=48 байт */
    printf("  a=%p (size~100 --> SC[6]=112 B)\n", a);
    printf("  b=%p (size~500 --> SC[15]=512 B)\n", b);
    printf("  c=%p (size~40  --> SC[2]=48 B)\n",  c);
    mem_show();

    printf("--- Звільняємо b (512 B), залишаємо a та c ---\n");
    mem_free(b);
    mem_show();

    printf("--- mem_realloc: a 100-->50 (in-place, SC[6] вже >= 50) ---\n");
    a = mem_realloc(a, 50);
    printf("  a після realloc(50)=%p\n", a);
    mem_show();

    printf("--- Звільняємо a і c --> slab-и мають стати порожніми ---\n");
    mem_free(a);
    mem_free(c);
    mem_show();

    printf("--- Велика алокація (32 КБ, виходить за межі slab-класів) ---\n");
    void *big = mem_alloc(32 * 1024);
    printf("  big=%p\n", big);
    mem_show();
    mem_free(big);
    mem_show();

    printf("--- Тест size-класів ---\n");
    {
        static const size_t test_sizes[] = {
            1,16,17,128,129,256,257,512,1024,4096,8192,16384,16385,65536
        };
        for (size_t ti = 0; ti < sizeof(test_sizes)/sizeof(test_sizes[0]); ti++) {
            size_t   sz = test_sizes[ti];
            unsigned sc = sc_index(sz);
            if (sc < NUM_SC)
                printf("  sc_index(%6zu) = %2u -> obj_size=%zu\n", sz, sc, sc_sizes[sc]);
            else
                printf("  sc_index(%6zu) = LARGE (> sc_sizes[35]=%zu)\n", sz, sc_sizes[NUM_SC-1]);
        }
    }

    printf("\n--- Автоматичний тестер (%d ітерацій) ---\n", ITERATIONS);
    test_run();

    return 0;
}
