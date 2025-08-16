from z3 import Optimize, Int, Or

def minutes(h, m):
    return h * 60 + m

def to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Work hours and meeting duration
    work_start = minutes(9, 0)
    work_end = minutes(17, 0)
    duration = 60

    # Busy schedules (Monday) for James and John
    james_busy = [
        (minutes(11, 30), minutes(12, 0)),
        (minutes(14, 30), minutes(15, 0)),
    ]
    john_busy = [
        (minutes(9, 30), minutes(11, 0)),
        (minutes(11, 30), minutes(12, 0)),
        (minutes(12, 30), minutes(13, 30)),
        (minutes(14, 30), minutes(16, 30)),
    ]

    # Z3 model: start time in minutes from 00:00
    s = Int('s')
    opt = Optimize()

    # Within work hours
    opt.add(s >= work_start)
    opt.add(s + duration <= work_end)

    # No-overlap constraints with busy intervals (treat intervals as [start, end))
    def add_no_overlap(busy_list):
        for (bs, be) in busy_list:
            opt.add(Or(s + duration <= bs, s >= be))

    add_no_overlap(james_busy)
    add_no_overlap(john_busy)

    # Prefer earliest feasible start
    opt.minimize(s)

    if opt.check() == 1:  # sat
        model = opt.model()
        start = model[s].as_long()
        end = start + duration
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {to_hhmm(start)} (24-hour format)")
        print(f"End Time: {to_hhmm(end)} (24-hour format)")

if __name__ == "__main__":
    main()