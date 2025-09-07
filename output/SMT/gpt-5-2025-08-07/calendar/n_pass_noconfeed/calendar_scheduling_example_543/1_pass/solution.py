from z3 import Optimize, Int, Or

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_min(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    # Meeting parameters
    day_name = "Monday"
    work_start = to_min("09:00")
    work_end = to_min("17:00")
    duration = 60  # minutes

    # Busy schedules (absolute minutes from 00:00)
    james_busy = [
        (to_min("11:30"), to_min("12:00")),
        (to_min("14:30"), to_min("15:00")),
    ]
    john_busy = [
        (to_min("09:30"), to_min("11:00")),
        (to_min("11:30"), to_min("12:00")),
        (to_min("12:30"), to_min("13:30")),
        (to_min("14:30"), to_min("16:30")),
    ]

    # SMT model
    opt = Optimize()
    start = Int("start")

    # Within work hours
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)

    # No overlap with busy intervals (half-open intervals)
    def no_overlap(intervals):
        for bs, be in intervals:
            opt.add(Or(start + duration <= bs, start >= be))

    no_overlap(james_busy)
    no_overlap(john_busy)

    # Prefer earliest feasible start
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        s = model[start].as_long()
        e = s + duration
        time_range = f"{{{fmt_min(s)}:{fmt_min(e)}}}"
        print(day_name, time_range)
    else:
        print("No feasible solution found.")

if __name__ == "__main__":
    main()