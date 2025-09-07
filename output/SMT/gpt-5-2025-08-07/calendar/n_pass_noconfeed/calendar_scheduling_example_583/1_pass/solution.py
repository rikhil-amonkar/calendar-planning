from z3 import Optimize, Int, Or, And, sat

def fmt_minutes(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def add_no_overlap(opt, start_var, duration, busy_intervals):
    end_var = start_var + duration
    for (bstart, bend) in busy_intervals:
        # Meeting [start, end) must not overlap busy [bstart, bend)
        opt.add(Or(end_var <= bstart, start_var >= bend))

def main():
    # Meeting details
    day = "Monday"
    duration = 30  # minutes
    work_start = 9 * 60
    work_end = 17 * 60

    # Busy schedules (minutes since midnight)
    lisa_busy = [
        (9 * 60, 9 * 60 + 30),       # 09:00 - 09:30
        (10 * 60 + 30, 11 * 60),     # 10:30 - 11:00
        (14 * 60, 16 * 60),          # 14:00 - 16:00
    ]
    anthony_busy = [
        (9 * 60, 9 * 60 + 30),       # 09:00 - 09:30
        (11 * 60, 11 * 60 + 30),     # 11:00 - 11:30
        (12 * 60 + 30, 13 * 60 + 30),# 12:30 - 13:30
        (14 * 60, 15 * 60),          # 14:00 - 15:00
        (15 * 60 + 30, 16 * 60),     # 15:30 - 16:00
        (16 * 60 + 30, 17 * 60),     # 16:30 - 17:00
    ]

    # Z3 model
    opt = Optimize()
    start = Int("start")

    # Work hours constraint
    opt.add(And(start >= work_start, start + duration <= work_end))

    # No overlap with busy times
    add_no_overlap(opt, start, duration, lisa_busy)
    add_no_overlap(opt, start, duration, anthony_busy)

    # Earliest availability
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible meeting time found, though one was expected.")

    model = opt.model()
    s_val = model[start].as_long()
    e_val = s_val + duration

    # Output
    time_range = f"{{{fmt_minutes(s_val)}:{fmt_minutes(e_val)}}}"
    print(day)
    print(time_range)

if __name__ == "__main__":
    main()