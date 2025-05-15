from z3 import *

def main():
    s = Solver()
    S = Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020), 30-minute meeting
    s.add(S >= 540)
    s.add(S + 30 <= 1020)

    # Frank's preference: meeting must end by 9:30 (570 minutes)
    s.add(S + 30 <= 570)

    # Busy intervals for each participant (start, end) in minutes
    schedules = {
        'Emily': [(600, 630), (690, 750), (840, 900), (960, 990)],
        'Melissa': [(570, 600), (870, 900)],
        'Frank': [(600, 630), (660, 690), (750, 780), (810, 870), (900, 960), (990, 1020)]
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