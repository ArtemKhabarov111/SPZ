from typing import Optional
from dataclasses import dataclass


@dataclass
class PhysicalPage:
    ppn: int                         # Номер фізичної сторінки
    in_use: bool = False             # Використовується
    owner_pid: Optional[int] = None  # Який процес використовує
    owner_vpn: Optional[int] = None  # Яка віртуальна сторінка відображена

    def __str__(self):
        if self.in_use:
            return f"PPN={self.ppn}[PID={self.owner_pid},VPN={self.owner_vpn}]"
        return f"PPN={self.ppn}[free]"
