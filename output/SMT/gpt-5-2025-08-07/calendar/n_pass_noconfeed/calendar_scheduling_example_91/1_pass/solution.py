# Requires: z3-solver
from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Problem setup
    day = "Monday"
    work_start = minutes(9, 0)   # 09:00
    work_end   = minutes(17, 0)  # 17:00
    duration = 60  # one hour

    # Existing schedules (blocked intervals) as [start_min, end_min)
    danielle = [
        (minutes(9, 0),  minutes(10, 0)),
        (minutes(10, 30), minutes(11, 0)),
        (minutes(14, 30), minutes(15, 0)),
        (minutes(15, 30), minutes(16, 0)),
        (minutes(16, 30), minutes(17, 0)),
    ]
    bruce = [
        (minutes(11, 0),  minutes(11, 30)),
        (minutes(12, 30), minutes(13, 0)),
        (minutes(14, 0),  minutes(14, 30)),
        (minutes(15, 30), minutes(16, 0)),
    ]
    eric = [
        (minutes(9, 0),  minutes(9, 30)),
        (minutes(10, 0), minutes(11, 0)),
        (minutes(11, 30), minutes(13, 0)),
        (minutes(14, 30), minutes(15, 30)),
    ]

    s = Optimize()
    start = Int("start")
    end = start + duration

    # Working hours and discrete 30-minute grid preference
    s.add(start >= work_start)
    s.add(end <= work_end)
    s.add(start % 30 == 0)  # schedule on 30-minute boundaries

    # No overlap with any participant's blocked intervals
    def no_overlap_with(intervals):
        return [Or(end <= b_start, start >= b_end) for (b_start, b_end) in intervals]

    s.add(no_overlap_with(danielle))
    s.add(no_overlap_with(bruce))
    s.add(no_overlap_with(eric))

    # Prefer the earliest valid start time
    s.minimize(start)

    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        end_val = start_val + duration
        print(f"{day} {{{fmt(start_val)}:{fmt(end_val)}}}")
    else:
        print("No feasible time found")

if __name__ == "__main__":
    main()