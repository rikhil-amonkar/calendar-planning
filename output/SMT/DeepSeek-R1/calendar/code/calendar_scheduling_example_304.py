from z3 import *

def main():
    s = Solver()
    S = Int('S')  # Start time in minutes since midnight

    # Constraints for time within work hours and Janice's preference
    s.add(S >= 540)   # 9:00
    s.add(S + 30 <= 780)  # Meeting ends by 13:00

    # Busy intervals for each participant (start, end) in minutes since midnight
    schedules = {
        'Christine': [(570, 630), (720, 750), (780, 810), (870, 900), (960, 990)],
        'Bobby': [(720, 750), (870, 900)],
        'Elizabeth': [(540, 570), (690, 780), (810, 840), (900, 930), (960, 1020)],
        'Tyler': [(540, 660), (720, 750), (780, 810), (930, 960), (990, 1020)],
        'Edward': [(540, 570), (600, 660), (690, 840), (870, 930), (960, 1020)]
    }

    # Add constraints for each participant's busy times
    for intervals in schedules.values():
        for start, end in intervals:
            s.add(Or(S + 30 <= start, S >= end))

    if s.check() == sat:
        model = s.model()
        start = model[S].as_long()
        h = start // 60
        m = start % 60
        print(f"Monday {h:02d}:{m:02d} to {(start + 30) // 60:02d}:{(start + 30) % 60:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()