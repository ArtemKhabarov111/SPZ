from PageTable import PageTable
from WorkingSet import WorkingSet
from config import WS_CHANGE_INTERVAL


class Process:
    def __init__(self, pid: int, num_virtual_pages: int, ws_size: int):
        self.pid = pid
        self.num_virtual_pages = num_virtual_pages
        self.page_table = PageTable(num_virtual_pages)
        self.working_set = WorkingSet(num_virtual_pages, ws_size)

        # Статистика
        self.total_accesses = 0
        self.page_faults = 0
        self.reads = 0
        self.writes = 0
        self._accesses_since_ws_change = 0

    # Генерує наступне звернення. За потреби, еволюціонує робочий набір
    def tick_access(self) -> tuple:
        self._accesses_since_ws_change += 1
        if self._accesses_since_ws_change >= WS_CHANGE_INTERVAL:
            self.working_set.evolve()
            self._accesses_since_ws_change = 0
        return self.working_set.get_access()

    def fault_rate(self) -> float:
        if self.total_accesses == 0:
            return 0.0
        return self.page_faults / self.total_accesses * 100
