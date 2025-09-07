# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, Or, And, sat

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(mm):
    h = mm // 60
    m = mm % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Meeting parameters
    day = "Monday"
    work_start = to_minutes(9, 0)     # 09:00
    work_end   = to_minutes(17, 0)    # 17:00
    duration = 30                     # 30 minutes
    prefer_before = to_minutes(12, 30) # Preference: avoid after 12:30

    # Busy schedules (half-open intervals [start, end))
    jack_busy = [
        (to_minutes(9, 30),  to_minutes(10, 30)),
        (to_minutes(11, 0),  to_minutes(11, 30)),
        (to_minutes(12, 30), to_minutes(13, 0)),
        (to_minutes(14, 0),  to_minutes(14, 30)),
        (to_minutes(16, 0),  to_minutes(16, 30)),
    ]
    charlotte_busy = [
        (to_minutes(9, 30),  to_minutes(10, 0)),
        (to_minutes(10, 30), to_minutes(12, 0)),
        (to_minutes(12, 30), to_minutes(13, 30)),
        (to_minutes(14, 0),  to_minutes(16, 0)),
    ]

    # Z3 Optimize model
    opt = Optimize()
    start = Int("start")

    # Working hours and duration
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)

    # No overlap with busy intervals
    def no_overlap(intervals):
        return [Or(start + duration <= s, start >= e) for (s, e) in intervals]

    opt.add(no_overlap(jack_busy))
    opt.add(no_overlap(charlotte_busy))

    # Preference: avoid after 12:30 (soft); also minimize earliest start to break ties
    penalty = Int("penalty")
    opt.add(penalty >= 0)
    opt.add(penalty >= start - prefer_before)  # penalty = max(0, start - prefer_before)
    opt.minimize(penalty)
    opt.minimize(start)  # earliest possible time among equally good options

    if opt.check() != sat:
        print("No feasible meeting time found.")
        return

    model = opt.model()
    s = model[start].as_long()
    e = s + duration

    # Output
    time_range = f"{{{fmt_time(s)}:{fmt_time(e)}}}"
    print(day)
    print(time_range)

if __name__ == "__main__":
    main()