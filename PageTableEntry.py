from typing import Optional
from dataclasses import dataclass


@dataclass
class PageTableEntry:
    P: bool = False            # presence bit - сторінка присутня в пам'яті
    R: bool = False            # reference bit - до сторінки було звернення
    M: bool = False            # modification bit - сторінка модифікована (dirty)
    PPN: Optional[int] = None  # Номер фізичної сторінки
    in_fs: bool = False        # Вміст збережено у файловій системі
