from Algorithm import Algorithm
from Simulation import Simulation, verify_working_set_effect
from config import WORKING_SET_SIZE


def main():
    print("\n======================================================================")
    print("           Лабораторна робота №3 - Алгоритми заміни сторінок          ")
    print("      2. Алгоритми випадкової заміни сторінок та Clock (Годинник)     ")
    print("======================================================================\n")

    # Запуск обох алгоритмів
    for algo in [Algorithm.RANDOM, Algorithm.CLOCK]:
        sim = Simulation(algo, ws_size=WORKING_SET_SIZE, seed=1)
        report = sim.run()
        print(report)
        print()

    # Верифікація
    verify_working_set_effect()


if __name__ == "__main__":
    main()
