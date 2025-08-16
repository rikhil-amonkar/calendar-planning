# Requires: z3-solver (pip install z3-solver)
from z3 import Int, Or, Optimize

def minutes(h, m):
    return h * 60 + m

def fmt_hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Problem setup (Monday, work hours 09:00–17:00, 1-hour duration)
    day = "Monday"
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 60  # minutes

    # Busy schedules (start, end) in minutes from 00:00
    busy = {
        "Olivia": [
            (minutes(12, 30), minutes(13, 30)),
            (minutes(14, 30), minutes(15, 0)),
            (minutes(16, 30), minutes(17, 0)),
        ],
        "Anna": [
            # No meetings
        ],
        "Virginia": [
            (minutes(9, 0), minutes(10, 0)),
            (minutes(11, 30), minutes(16, 0)),
            (minutes(16, 30), minutes(17, 0)),
        ],
        "Paul": [
            (minutes(9, 0), minutes(9, 30)),
            (minutes(11, 0), minutes(11, 30)),
            (minutes(13, 0), minutes(14, 0)),
            (minutes(14, 30), minutes(16, 0)),
            (minutes(16, 30), minutes(17, 0)),
        ],
    }

    start = Int("start")

    opt = Optimize()
    # Working hours constraint
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)

    # No overlap with each participant's busy intervals
    for person, intervals in busy.items():
        for (b_start, b_end) in intervals:
            # Meeting [start, start+duration) must be fully before or after each busy interval [b_start, b_end)
            opt.add(Or(start + duration <= b_start, start >= b_end))

    # Prefer earliest feasible start time
    opt.minimize(start)

    if opt.check() != 1:  # sat == 1
        raise RuntimeError("No feasible solution found, but one was expected.")

    model = opt.model()
    start_min = model[start].as_long()
    end_min = start_min + duration

    # Output in required format
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_hhmm(start_min)} (24-hour format)")
    print(f"End Time: {fmt_hhmm(end_min)} (24-hour format)")

if __name__ == "__main__":
    main()