import random

from Process import Process
from Algorithm import Algorithm
from PhysicalPage import PhysicalPage
from typing import Optional, Dict, List


# Керує фізичними сторінками
# Реалізує алгоритми заміни Random та Clock
class Kernel:
    def __init__(self, num_physical_pages: int, algorithm: Algorithm):
        self.frames: List[PhysicalPage] = [
            PhysicalPage(ppn=i) for i in range(num_physical_pages)
        ]
        self.algorithm = algorithm
        self.clock_hand = 0  # Вказівник годинника

        # Статистика
        self.total_faults = 0
        self.replacements = 0
        self.dirty_evictions = 0
        self.events: List[str] = []

    # Обробка сторінкового промаху (знаходить вільну або звільняє зайняту сторінку)
    def handle_page_fault(self, processes: Dict[int, Process], faulting_pid: int, vpn: int):
        self.total_faults += 1
        process = processes[faulting_pid]

        victim = self._get_free_frame()
        if victim is None:
            # Якщо всі фізичні сторінки зайняті, то запускаємо алгоритм заміни
            if self.algorithm == Algorithm.RANDOM:
                victim = self._replace_random(processes)
            else:
                victim = self._replace_clock(processes)
            self.replacements += 1

        # Створення відображення (віртуальна сторінка --> фізична сторінка)
        pte = process.page_table[vpn]
        pte.P = True
        pte.R = False
        pte.M = False
        pte.PPN = victim.ppn
        victim.in_use = True
        victim.owner_pid = faulting_pid
        victim.owner_vpn = vpn

        self.events.append(
            f"FAULT PID={faulting_pid} VPN={vpn:2d} --> PPN={victim.ppn:2d}"
            f"[{'loaded from FS' if pte.in_fs else 'new page'}]"
        )

    # Службові методи
    def _get_free_frame(self) -> Optional[PhysicalPage]:
        for f in self.frames:
            if not f.in_use:
                return f
        return None

    # Виселяє власника фізичної сторінки. Dirty --> збереження у ФС
    def _evict(self, frame: PhysicalPage, processes: Dict[int, Process]) -> PhysicalPage:
        owner = processes[frame.owner_pid]
        pte = owner.page_table[frame.owner_vpn]
        dirty = pte.M
        if dirty:
            pte.in_fs = True  # вміст збережено у ФС (dirty page out)
            self.dirty_evictions += 1

        self.events.append(
            f"EVICT PID={frame.owner_pid} VPN={frame.owner_vpn:2d} "
            f"PPN={frame.ppn:2d} {'(dirty-->FS)' if dirty else '(clean)'}"
        )

        # Знищення відображення
        pte.P = False
        pte.R = False
        pte.M = False
        pte.PPN = None
        frame.in_use = False
        frame.owner_pid = None
        frame.owner_vpn = None
        return frame

    # Алгоритм випадкової заміни (Random). Не враховує R та M
    # Вибирає довільну зайняту фізичну сторінку і виселяє її власника
    def _replace_random(self, processes: Dict[int, Process]) -> PhysicalPage:
        in_use = [f for f in self.frames if f.in_use]
        victim = random.choice(in_use)
        return self._evict(victim, processes)

    # Алгоритм Годинник (Clock). Вказівник (clock_hand) обходить фізичні сторінки по колу
    # R == 0 --> ця сторінка є жертвою (не було звернення = "стара")
    # R == 1 --> даємо "другий шанс": скидаємо R := 0 і рухаємось далі
    # Гарантовано знайде жертву за не більше ніж 2 повних оберти
    def _replace_clock(self, processes: Dict[int, Process]) -> PhysicalPage:
        checked = 0
        while True:
            frame = self.frames[self.clock_hand]
            self.clock_hand = (self.clock_hand + 1) % len(self.frames)

            if not frame.in_use:
                continue  # вільна

            pte = processes[frame.owner_pid].page_table[frame.owner_vpn]
            if pte.R == 0:
                # Жертва знайдена
                return self._evict(frame, processes)
            else:
                # Другий шанс: скидаємо R
                pte.R = False

            checked += 1
            if checked > 2 * len(self.frames):
                # На випадок нескінченного циклу (всі R=1 --> після двох обертів всі R=0)
                return self._evict(frame, processes)

    # Стан пам'яті
    def free_frames(self) -> int:
        return sum(1 for f in self.frames if not f.in_use)

    def used_frames(self) -> int:
        return len(self.frames) - self.free_frames()
