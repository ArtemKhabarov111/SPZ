from typing import List
from PageTableEntry import PageTableEntry


class PageTable:
    def __init__(self, size: int):
        self.entries: List[PageTableEntry] = [PageTableEntry() for _ in range(size)]

    def __getitem__(self, vpn: int) -> PageTableEntry:
        return self.entries[vpn]

    def mapped_count(self) -> int:
        return sum(1 for e in self.entries if e.P)
