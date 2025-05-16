from z3 import *

def main():
    s = Solver()
    S = Int('S')  # Start time in minutes since midnight (Monday)

    # Work hours constraint: 9:00 (540) to 17:00 (1020), 30-minute meeting
    s.add(S >= 540)
    s.add(S + 30 <= 1020)

    # Doris's schedule constraints and preference
    # Busy intervals on Monday: 540-690, 720-750, 810-960, 990-1020
    # Preference: meeting must end by 14:00 (840)
    
    # Must start after 11:30 (690) to avoid 9:00-11:30 busy
    s.add(S >= 690)
    
    # Avoid 12:00-12:30 (720-750): meeting must end by 720 or start after 750
    s.add(Or(S + 30 <= 720, S >= 750))
    
    # Avoid 13:30-16:00 (810-960): meeting must end by 810 (13:30)
    s.add(S + 30 <= 810)
    
    # Jean has no meetings on Monday (only busy on Tuesday)

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