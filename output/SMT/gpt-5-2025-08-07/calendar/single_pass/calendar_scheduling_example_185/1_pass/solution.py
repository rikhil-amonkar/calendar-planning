from z3 import Int, Optimize, Or, And, Mod

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Meeting parameters
    day = "Monday"
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 30  # half an hour

    # Busy schedules (half-open intervals [start, end))
    kimberly_busy = [
        (minutes(10, 0), minutes(10, 30)),
        (minutes(11, 0), minutes(12, 0)),
        (minutes(16, 0), minutes(16, 30)),
    ]
    megan_busy = []  # Megan has no meetings the whole day
    marie_busy = [
        (minutes(10, 0), minutes(11, 0)),
        (minutes(11, 30), minutes(15, 0)),
        (minutes(16, 0), minutes(16, 30)),
    ]
    diana_busy = [
        (minutes(9, 30), minutes(10, 0)),
        (minutes(10, 30), minutes(14, 30)),
        (minutes(15, 30), minutes(17, 0)),
    ]

    # Z3 variables
    start = Int("start")

    opt = Optimize()

    # Meeting must be within work hours and aligned to 30-minute increments
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)
    opt.add(Mod(start, 30) == 0)

    # No overlap constraints: meeting [start, start+duration) must not overlap each busy interval
    def no_overlap_constraints(busy_list):
        return [Or(start + duration <= s, start >= e) for (s, e) in busy_list]

    all_busy = kimberly_busy + megan_busy + marie_busy + diana_busy
    for c in no_overlap_constraints(all_busy):
        opt.add(c)

    # Preference: Megan would like to avoid meetings before 10:00 (soft constraint)
    opt.add_soft(start >= minutes(10, 0), weight="1", id="megan_pref")

    # Choose the earliest feasible time that best satisfies preferences
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible meeting time found (unexpected based on problem statement).")

    model = opt.model()
    start_val = model[start].as_long()
    end_val = start_val + duration

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_time(start_val)}")
    print(f"End Time: {fmt_time(end_val)}")

if __name__ == "__main__":
    main()