from z3 import *

def main():
    s = Solver()
    S = Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020), 30-minute meeting
    s.add(S >= 540)
    s.add(S + 30 <= 1020)

    # Jose's preference: end by 15:30 (930 minutes)
    s.add(S + 30 <= 930)

    # Busy intervals for each participant (start, end) in minutes
    schedules = {
        'Jose': [(660, 690), (750, 780)],
        'Keith': [(840, 870), (900, 930)],
        'Logan': [(540, 600), (720, 750), (900, 930)],
        'Megan': [(540, 630), (660, 720), (780, 810), (870, 990)],
        'Gary': [(540, 570), (600, 630), (690, 780), (810, 840), (870, 990)],
        'Bobby': [(660, 690), (720, 750), (780, 960)]
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