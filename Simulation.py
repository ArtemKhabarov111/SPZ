import random
from typing import Dict, List

from Algorithm import Algorithm
from Kernel import Kernel
from MMU import MMU
from Process import Process
from config import *


class Simulation:
    def __init__(self, algorithm: Algorithm, ws_size: int = WORKING_SET_SIZE, seed: int = 42):
        random.seed(seed)
        self.algorithm = algorithm
        self.ws_size = ws_size
        self.mmu = MMU()
        self.kernel = Kernel(NUM_PHYSICAL_PAGES, algorithm)
        self.processes: Dict[int, Process] = {
            pid: Process(pid, VIRTUAL_PAGES, ws_size)
            for pid in range(NUM_PROCESSES)
        }
        self.snapshots: List[dict] = []

    def run(self) -> str:
        proc_list = list(self.processes.values())
        proc_idx = 0
        total_done = 0

        while total_done < TOTAL_ACCESSES:
            process = proc_list[proc_idx % len(proc_list)]
            proc_idx += 1

            # Квант
            for _ in range(QUANTUM):
                if total_done >= TOTAL_ACCESSES:
                    break

                vpn, is_write = process.tick_access()
                process.total_accesses += 1
                if is_write:
                    process.writes += 1
                else:
                    process.reads += 1
                total_done += 1

                ppn, fault = self.mmu.translate(process, vpn, is_write)
                if fault:
                    process.page_faults += 1
                    self.kernel.handle_page_fault(self.processes, process.pid, vpn)

                    # Після відображення MMU виконує звернення
                    pte = process.page_table[vpn]
                    pte.R = True
                    if is_write:
                        pte.M = True

            # Знімок кожні 500 звернень
            if total_done % 500 < QUANTUM or total_done >= TOTAL_ACCESSES:
                self.snapshots.append({
                    "t": total_done,
                    "faults": self.kernel.total_faults,
                    "replacements": self.kernel.replacements,
                    "free_frames": self.kernel.free_frames(),
                })

        return self._build_report()

    # Звіт
    def _build_report(self) -> str:
        lines = []
        sep = "======================================================================"

        lines.append(sep)
        lines.append(f"Алгоритм: {self.algorithm.value}")
        lines.append(f"Фізичних сторінок: {NUM_PHYSICAL_PAGES}  |  Процесів: {NUM_PROCESSES}  |  "
                     f"Вірт. сторінок/процес: {VIRTUAL_PAGES}")
        lines.append(f"Розмір робочого набору: {self.ws_size}  |  Всього звернень: {TOTAL_ACCESSES}")
        lines.append(sep)

        # Прогрес
        lines.append("\n                    Прогрес симуляції:")
        lines.append(f"{'Час':>8} {'Промахи':>14} {'Заміни':>12} {'Вільних кадрів':>18}")
        lines.append("  " + "-" * 55)
        for s in self.snapshots:
            lines.append(
                f"{s['t']:>8} {s['faults']:>12} {s['replacements']:>12} {s['free_frames']:>12}/{NUM_PHYSICAL_PAGES}"
            )

        # Статистика процесів
        lines.append(f"\n                                   Статистика процесів:")
        lines.append(f"{'PID':>9} {'Звернень':>14} {'Читань':>11} "
                     f"{'Записів':>12} {'Промахів':>13} {'Частота промахів':>20}")
        lines.append("  " + "-" * 85)
        for pid, proc in self.processes.items():
            lines.append(
                f"{pid:>8} {proc.total_accesses:>12} {proc.reads:>12} {proc.writes:>12} {proc.page_faults:>12} "
                f"{proc.fault_rate():>17.2f}%"
            )

        # Підсумок
        total_accesses = sum(p.total_accesses for p in self.processes.values())
        total_faults = self.kernel.total_faults
        lines.append("\n" + sep)
        lines.append(f"Загальних звернень: {total_accesses}")
        lines.append(f"Загальних промахів: {total_faults}")
        lines.append(f"Загальна частота промахів: {total_faults / total_accesses * 100:.2f}%")
        lines.append(f"Замін сторінок: {self.kernel.replacements}")
        lines.append(f"Брудних виселень (--> ФС): {self.kernel.dirty_evictions}")
        lines.append(sep)

        return "\n".join(lines)


# Перевірка правильності (зміна розміру робочого набору)
# При збільшенні робочого набору частота промахів має зростати
# Random має давати більше промахів, ніж Clock
def verify_working_set_effect():
    print("\n" + "======================================================================")
    print("     Перевірка впливу розміру робочого набору на частоту промахів")
    print("======================================================================")
    print(f"{'WS':>8} {'Random промахи%':>22} {'Clock промахи%':>16} {'Різниця':>13}")
    print("  " + "-" * 64)

    for ws in [4, 6, 8, 10, 14, 18]:
        sim_r = Simulation(Algorithm.RANDOM, ws_size=ws, seed=2)
        sim_c = Simulation(Algorithm.CLOCK, ws_size=ws, seed=2)
        sim_r.run()
        sim_c.run()

        fr_r = sim_r.kernel.total_faults / TOTAL_ACCESSES * 100
        fr_c = sim_c.kernel.total_faults / TOTAL_ACCESSES * 100
        diff = fr_r - fr_c
        print(f"{ws:>8} {fr_r:>16.2f}% {fr_c:>16.2f}% {diff:>+16.2f}%")
