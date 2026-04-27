import random

from config import LOCALITY_PROBABILITY, WRITE_PROBABILITY


# 90% звернень іде до сторінок робочого набору
# 10% — до будь-яких сторінок віртуального простору
# Робочий набір частково змінюється кожні WS_CHANGE_INTERVAL звернень
class WorkingSet:
    def __init__(self, total_pages: int, ws_size: int):
        self.total_pages = total_pages
        self.ws_size = ws_size
        self.pages: set = set(random.sample(range(total_pages), ws_size))

    # Повертає (vpn, is_write) з урахуванням локальності
    def get_access(self) -> tuple:
        if random.random() < LOCALITY_PROBABILITY and self.pages:
            vpn = random.choice(list(self.pages))
        else:
            vpn = random.randint(0, self.total_pages - 1)
        is_write = random.random() < WRITE_PROBABILITY
        return vpn, is_write

    # Частково оновлює робочий набір. Приблизно 1/3 сторінок змінюється
    def evolve(self):
        n_change = max(1, self.ws_size // 3)
        n_change = min(n_change, len(self.pages))
        to_remove = random.sample(list(self.pages), n_change)
        available = list(set(range(self.total_pages)) - self.pages)
        if available:
            to_add = random.sample(available, min(n_change, len(available)))
            for p in to_remove:
                self.pages.discard(p)
            for p in to_add:
                self.pages.add(p)
