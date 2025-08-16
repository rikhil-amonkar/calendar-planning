from z3 import Optimize, Int, Or, sat

def to_minutes(hh_mm):
    hh, mm = map(int, hh_mm.split(":"))
    return hh * 60 + mm

def fmt_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

def add_no_overlap(opt, start_var, duration, busy_intervals):
    for (b_start, b_end) in busy_intervals:
        # No overlap with [b_start, b_end)
        opt.add(Or(start_var + duration <= b_start, start_var >= b_end))

def main():
    # Problem setup
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30

    # Busy schedules (all times on Monday)
    Melissa = [(to_minutes("10:00"), to_minutes("11:00")),
               (to_minutes("12:30"), to_minutes("14:00")),
               (to_minutes("15:00"), to_minutes("15:30"))]

    Gregory = [(to_minutes("12:30"), to_minutes("13:00")),
               (to_minutes("15:30"), to_minutes("16:00"))]

    Victoria = [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:30"), to_minutes("11:30")),
                (to_minutes("13:00"), to_minutes("14:00")),
                (to_minutes("14:30"), to_minutes("15:00")),
                (to_minutes("15:30"), to_minutes("16:30"))]

    Thomas = [(to_minutes("10:00"), to_minutes("12:00")),
              (to_minutes("12:30"), to_minutes("13:00")),
              (to_minutes("14:30"), to_minutes("16:00"))]

    Jennifer = [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:00"), to_minutes("10:30")),
                (to_minutes("11:00"), to_minutes("13:00")),
                (to_minutes("13:30"), to_minutes("14:30")),
                (to_minutes("15:00"), to_minutes("15:30")),
                (to_minutes("16:00"), to_minutes("16:30"))]

    # Wayne and Catherine are free all day
    Wayne = []
    Catherine = []

    # Z3 Optimize (to model Wayne's preference as a soft constraint)
    opt = Optimize()
    start = Int("start")

    # Work hours and duration bounds
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)

    # No-overlap constraints for each participant
    for busy in [Wayne, Melissa, Catherine, Gregory, Victoria, Thomas, Jennifer]:
        add_no_overlap(opt, start, duration, busy)

    # Preference: Wayne would like to avoid meetings before 14:00
    opt.add_soft(start >= to_minutes("14:00"), "1")

    # Among solutions that satisfy preferences, pick the earliest start
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible meeting time found.")

    m = opt.model()
    s_val = m.eval(start).as_long()
    e_val = s_val + duration

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_time(s_val)}")
    print(f"End Time: {fmt_time(e_val)}")

if __name__ == "__main__":
    main()