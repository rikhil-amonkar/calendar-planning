from z3 import Optimize, Int, Or, sat

def minutes(h, m=0):
    return h * 60 + m

def fmt_time(t):
    return f"{t // 60:02d}:{t % 60:02d}"

def main():
    day = "Monday"
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 30  # minutes

    # Busy intervals per participant on Monday (start, end) in minutes since 00:00
    busy = {
        "Tyler": [],
        "Kelly": [],
        "Stephanie": [
            (minutes(11, 0), minutes(11, 30)),
            (minutes(14, 30), minutes(15, 0)),
        ],
        "Hannah": [],
        "Joe": [
            (minutes(9, 0), minutes(9, 30)),
            (minutes(10, 0), minutes(12, 0)),
            (minutes(12, 30), minutes(13, 0)),
            (minutes(14, 0), minutes(17, 0)),
        ],
        "Diana": [
            (minutes(9, 0), minutes(10, 30)),
            (minutes(11, 30), minutes(12, 0)),
            (minutes(13, 0), minutes(14, 0)),
            (minutes(14, 30), minutes(15, 30)),
            (minutes(16, 0), minutes(17, 0)),
        ],
        "Deborah": [
            (minutes(9, 0), minutes(10, 0)),
            (minutes(10, 30), minutes(12, 0)),
            (minutes(12, 30), minutes(13, 0)),
            (minutes(13, 30), minutes(14, 0)),
            (minutes(14, 30), minutes(15, 30)),
            (minutes(16, 0), minutes(16, 30)),
        ],
    }

    # Create optimizer to find the earliest feasible start
    opt = Optimize()
    start = Int("start")
    end = Int("end")

    opt.add(end == start + duration)
    opt.add(start >= work_start, end <= work_end)

    # Non-overlap constraints with all busy intervals of all participants
    for intervals in busy.values():
        for (b_start, b_end) in intervals:
            opt.add(Or(end <= b_start, start >= b_end))

    # Minimize the start time to get the earliest meeting
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible meeting time found, but the task guarantees a solution.")

    model = opt.model()
    s_val = model[start].as_long()
    e_val = model[end].as_long()

    # Output: Day and time range in {HH:MM:HH:MM}
    print(f"{day} {{{fmt_time(s_val)}:{fmt_time(e_val)}}}")

if __name__ == "__main__":
    main()