from z3 import *

def main():
    s = Solver()
    D = Int('D')  # 0: Monday, 1: Tuesday, 2: Wednesday
    S = Int('S')  # Start time in minutes since midnight

    # Day must be Monday (0) due to John's constraints
    s.add(D == 0)
    # Time must be within work hours on Monday and John's preference (end by 14:30)
    s.add(S >= 540)   # 9:00
    s.add(S + 30 <= 870)  # 14:30 end

    # Jennifer's busy intervals on Monday (minutes since midnight)
    jennifer_busy = [(540, 660), (690, 780), (810, 870), (900, 1020)]

    # Ensure meeting doesn't overlap with Jennifer's schedule
    for start, end in jennifer_busy:
        s.add(Or(S + 30 <= start, S >= end))

    if s.check() == sat:
        model = s.model()
        start_time = model[S].as_long()
        h = start_time // 60
        m = start_time % 60
        print(f"Monday {h:02d}:{m:02d} to {(start_time + 30) // 60:02d}:{(start_time + 30) % 60:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()