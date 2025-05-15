from z3 import *

def main():
    s = Solver()
    S = Int('S')  # Start time in minutes since midnight

    # Work hours constraint: 9:00 (540) to 17:00 (1020), 1-hour meeting
    s.add(S >= 540)
    s.add(S + 60 <= 1020)

    # Busy intervals for each participant (start, end) in minutes
    schedules = {
        'Danielle': [(540, 600), (630, 660), (870, 900), (930, 960), (990, 1020)],
        'Bruce': [(660, 690), (750, 780), (840, 870), (930, 960)],
        'Eric': [(540, 570), (600, 660), (690, 780), (870, 930)]
    }

    # Add constraints for each participant's busy times
    for intervals in schedules.values():
        for start, end in intervals:
            s.add(Or(S + 60 <= start, S >= end))

    if s.check() == sat:
        model = s.model()
        start = model[S].as_long()
        h = start // 60
        m = start % 60
        print(f"Monday {h:02d}:{m:02d} to {(start + 60) // 60:02d}:{(start + 60) % 60:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()