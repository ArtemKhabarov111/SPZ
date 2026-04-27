from Process import Process


# Транслює (pid, vpn) --> ppn. Встановлює біти R та M.
# При відсутній сторінці генерує сторінковий промах (повертає fault=True).
class MMU:
    @staticmethod
    def translate(process: Process, vpn: int, is_write: bool) -> tuple:
        pte = process.page_table[vpn]
        if not pte.P:
            return None, True  # page fault
        pte.R = True           # MMU встановлює R при кожному зверненні
        if is_write:
            pte.M = True       # MMU встановлює M при записі
        return pte.PPN, False
