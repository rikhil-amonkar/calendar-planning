from z3 import *

def main():
    solver = Solver()
    start = Int('start')

    # Work hours from 9:00 (540) to 17:00 (1020)
    # Albert's blocked periods:
    # 9:00-10:00 (540-600)
    # 10:30-12:00 (630-720)
    # 15:00-16:30 (900-990)
    # Albert can't meet after 11:00 (660)
    # Meeting duration is 30 minutes.

    # Constraints to avoid overlapping with Albert's blocked periods and end by 11:00
    solver.add(start >= 540)
    solver.add(start + 30 <= 660)  # end by 11:00
    # Avoid overlapping with Blocked1 (540-600)
    solver.add(Or(start >= 600, start + 30 <= 540))
    # Avoid overlapping with Blocked2 (630-720)
    solver.add(Or(start >= 720, start + 30 <= 630))
    # Avoid overlapping with Blocked3 (900-990)
    solver.add(Or(start >= 990, start + 30 <= 900))

    if solver.check() == sat:
        model = solver.model()
        start_time = model[start].as_long()
        end_time = start_time + 30
        # Convert to HH:MM
        def to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        start_str = to_time(start_time)
        end_str = to_time(end_time)
        day = "Monday"
        print(f"{start_str}:{end_str} {day}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()