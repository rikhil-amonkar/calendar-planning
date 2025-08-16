from z3 import Int, Optimize, And, Or, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]

    # Meeting duration: 30 minutes
    duration = 30

    # Work hours: 09:00 to 17:00
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)

    # Busy schedules by day (union of all participants)
    # Julie: no meetings.
    # Ruth:
    #   Mon: 09:00-17:00
    #   Tue: 09:00-17:00
    #   Wed: 09:00-17:00
    #   Thu: 09:00-11:00, 11:30-14:30, 15:00-17:00
    busy = {
        0: [(minutes(9,0), minutes(17,0))],
        1: [(minutes(9,0), minutes(17,0))],
        2: [(minutes(9,0), minutes(17,0))],
        3: [
            (minutes(9,0),  minutes(11,0)),
            (minutes(11,30), minutes(14,30)),
            (minutes(15,0),  minutes(17,0)),
        ],
    }

    # Variables
    day = Int("day")
    start = Int("start")
    end = Int("end")

    opt = Optimize()

    # Day within Monday-Thursday
    opt.add(And(day >= 0, day <= 3))

    # Meeting within work hours and correct duration
    opt.add(And(start >= work_start, end == start + duration, end <= work_end))

    # No overlap with busy intervals on the chosen day
    for d in range(4):
        for (bs, be) in busy[d]:
            # If it's not this day, no constraint; if it is, enforce non-overlap
            opt.add(Or(day != d, end <= bs, start >= be))

    # Preference: Julie would like to avoid meetings on Thursday before 11:30
    # Soft constraint: if day == Thursday (3), prefer start >= 11:30
    opt.add_soft(Or(day != 3, start >= minutes(11,30)), weight=1)

    if opt.check() != sat:
        raise RuntimeError("No feasible schedule found")

    model = opt.model()
    d_val = model[day].as_long()
    s_val = model[start].as_long()
    e_val = model[end].as_long()

    print("SOLUTION:")
    print(f"Day: {day_names[d_val]}")
    print(f"Start Time: {fmt_time(s_val)}")
    print(f"End Time: {fmt_time(e_val)}")

if __name__ == "__main__":
    main()