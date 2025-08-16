# Requires: z3-solver
# pip install z3-solver

from z3 import Int, Solver, And, Or, Not

def minutes_to_time(m):
    h = m // 60
    mins = m % 60
    return f"{h:02d}:{mins:02d}"

def main():
    # Problem parameters
    day = "Monday"
    work_start = 9 * 60   # 09:00 -> 540
    work_end = 17 * 60    # 17:00 -> 1020
    duration = 30         # minutes

    # Busy intervals as (start_min, end_min) in minutes from 00:00
    busy = {
        "Walter": [],
        "Cynthia": [
            (9*60, 9*60+30),     # 09:00-09:30
            (10*60, 10*60+30),   # 10:00-10:30
            (13*60+30, 14*60+30),# 13:30-14:30
            (15*60, 16*60),      # 15:00-16:00
        ],
        "Ann": [
            (10*60, 11*60),      # 10:00-11:00
            (13*60, 13*60+30),   # 13:00-13:30
            (14*60, 15*60),      # 14:00-15:00
            (16*60, 16*60+30),   # 16:00-16:30
        ],
        "Catherine": [
            (9*60, 11*60+30),    # 09:00-11:30
            (12*60+30, 13*60+30),# 12:30-13:30
            (14*60+30, 17*60),   # 14:30-17:00
        ],
        "Kyle": [
            (9*60, 9*60+30),     # 09:00-09:30
            (10*60, 11*60+30),   # 10:00-11:30
            (12*60, 12*60+30),   # 12:00-12:30
            (13*60, 14*60+30),   # 13:00-14:30
            (15*60, 16*60),      # 15:00-16:00
        ],
    }

    # Z3 variables
    start = Int("start")
    end = Int("end")

    s = Solver()

    # Time window and duration constraints
    s.add(start >= work_start)
    s.add(end == start + duration)
    s.add(end <= work_end)

    # Optional: restrict to 30-minute grid (common for calendars)
    s.add(start % 30 == 0)

    # No overlap with any participant's busy intervals
    for person, intervals in busy.items():
        for (b_start, b_end) in intervals:
            # Meeting [start, end) does not overlap busy [b_start, b_end)
            s.add(Or(end <= b_start, start >= b_end))

    if s.check() != sat:
        raise RuntimeError("No feasible solution found, but the problem statement guarantees one exists.")

    m = s.model()
    start_min = m[start].as_long()
    end_min = m[end].as_long()

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_time(start_min)} (24-hour format)")
    print(f"End Time: {minutes_to_time(end_min)} (24-hour format)")

if __name__ == "__main__":
    main()