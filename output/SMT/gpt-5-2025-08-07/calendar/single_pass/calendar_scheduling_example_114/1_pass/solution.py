from z3 import Optimize, Int, Or

def T(h, m):
    return h * 60 + m

def minutes_to_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Work hours and meeting duration
    work_start = T(9, 0)    # 09:00
    work_end   = T(17, 0)   # 17:00
    duration = 60           # 1 hour

    # Busy schedules (Monday) as half-open intervals [start, end)
    busy = {
        "Stephanie": [(T(10, 0), T(10, 30)), (T(16, 0), T(16, 30))],
        "Cheryl":    [(T(10, 0), T(10, 30)), (T(11, 30), T(12, 0)),
                      (T(13, 30), T(14, 0)), (T(16, 30), T(17, 0))],
        "Bradley":   [(T(9, 30), T(10, 0)), (T(10, 30), T(11, 30)),
                      (T(13, 30), T(14, 0)), (T(14, 30), T(15, 0)), (T(15, 30), T(17, 0))],
        "Steven":    [(T(9, 0), T(12, 0)), (T(13, 0), T(13, 30)), (T(14, 30), T(17, 0))]
    }

    # Z3 model
    start = Int("start")
    opt = Optimize()

    # Work hours constraints
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)

    # Non-overlap constraints with all busy intervals
    for person, intervals in busy.items():
        for (b_start, b_end) in intervals:
            # Meeting [start, start+duration) does not intersect [b_start, b_end)
            opt.add(Or(start + duration <= b_start, start >= b_end))

    # Prefer the earliest possible meeting time
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        s = model[start].as_long()
        e = s + duration
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {minutes_to_str(s)} (24-hour format)")
        print(f"End Time: {minutes_to_str(e)} (24-hour format)")
    else:
        # Per problem statement, a solution exists; this is a fallback.
        print("SOLUTION:")
        print("Day: Monday")
        print("Start Time: 00:00 (24-hour format)")
        print("End Time: 00:00 (24-hour format)")

if __name__ == "__main__":
    main()