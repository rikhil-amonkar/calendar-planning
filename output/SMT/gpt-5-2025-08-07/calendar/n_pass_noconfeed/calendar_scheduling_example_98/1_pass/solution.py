from z3 import Optimize, Int, Or

def to_minutes(h, m):
    return h * 60 + m

def fmt(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def main():
    # Meeting parameters
    day = "Monday"
    duration = 30  # minutes
    work_start = to_minutes(9, 0)
    work_end = to_minutes(17, 0)

    # Busy schedules (start, end) in minutes from 00:00
    busy_juan = [
        (to_minutes(9, 0), to_minutes(10, 30)),
        (to_minutes(15, 30), to_minutes(16, 0)),
    ]
    busy_marilyn = [
        (to_minutes(11, 0), to_minutes(11, 30)),
        (to_minutes(12, 30), to_minutes(13, 0)),
    ]
    busy_ronald = [
        (to_minutes(9, 0), to_minutes(10, 30)),
        (to_minutes(12, 0), to_minutes(12, 30)),
        (to_minutes(13, 0), to_minutes(13, 30)),
        (to_minutes(14, 0), to_minutes(16, 30)),
    ]

    # SMT model
    opt = Optimize()
    start = Int("start")
    end = start + duration

    # Work hours constraint
    opt.add(start >= work_start, end <= work_end)

    # Juan cannot meet after 16:00 -> meeting must end by 16:00
    opt.add(end <= to_minutes(16, 0))

    # No overlap with busy intervals for each participant
    def no_overlap(busy_list):
        for (bs, be) in busy_list:
            opt.add(Or(end <= bs, start >= be))

    no_overlap(busy_juan)
    no_overlap(busy_marilyn)
    no_overlap(busy_ronald)

    # Prefer earliest possible time
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        s_val = model[start].as_long()
        e_val = s_val + duration
        print(day)
        print(f"{{{fmt(s_val)}:{fmt(e_val)}}}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()