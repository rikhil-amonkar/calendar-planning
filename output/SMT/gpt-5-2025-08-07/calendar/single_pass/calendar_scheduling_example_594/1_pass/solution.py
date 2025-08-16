from z3 import Optimize, Int, Or

def to_minutes(h, m):
    return h * 60 + m

def from_minutes(total):
    h = total // 60
    m = total % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    # Problem setup (given)
    day = "Monday"
    work_start = to_minutes(9, 0)
    work_end = to_minutes(17, 0)
    duration = 30  # minutes

    # Busy schedules (inclusive of start, exclusive of end)
    schedules = {
        "Adam": [
            (to_minutes(9, 30), to_minutes(10, 0)),
            (to_minutes(12, 30), to_minutes(13, 0)),
            (to_minutes(14, 30), to_minutes(15, 0)),
            (to_minutes(16, 30), to_minutes(17, 0)),
        ],
        "Roy": [
            (to_minutes(10, 0), to_minutes(11, 0)),
            (to_minutes(11, 30), to_minutes(13, 0)),
            (to_minutes(13, 30), to_minutes(14, 30)),
            (to_minutes(16, 30), to_minutes(17, 0)),
        ],
    }

    # Z3 optimization: earliest feasible start time
    opt = Optimize()
    start = Int("start")

    # Within work hours
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)

    # No overlap with any participant's busy intervals: [start, start+duration) must not intersect [b_start, b_end)
    for person, intervals in schedules.items():
        for b_start, b_end in intervals:
            opt.add(Or(start + duration <= b_start, start >= b_end))

    # Earliest availability
    opt.minimize(start)

    if opt.check().r == 1:  # sat
        model = opt.model()
        s = model[start].as_long()
        e = s + duration
        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {from_minutes(s)} (24-hour format)")
        print(f"End Time: {from_minutes(e)} (24-hour format)")
    else:
        # Given the problem guarantees a solution, this branch should not occur.
        raise RuntimeError("No feasible schedule found.")

if __name__ == "__main__":
    schedule_meeting()