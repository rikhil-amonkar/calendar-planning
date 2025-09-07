from z3 import *

def to_minutes(hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def no_overlap_constraints(start, duration, busy_intervals):
    constraints = []
    end = start + duration
    for (b_start, b_end) in busy_intervals:
        # Meeting [start, end) must not intersect [b_start, b_end)
        constraints.append(Or(end <= b_start, start >= b_end))
    return constraints

def main():
    # Work hours and meeting duration
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 60  # one hour

    # Participants' busy schedules (Monday)
    julie_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:30"), to_minutes("14:00")),
        (to_minutes("16:00"), to_minutes("17:00")),
    ]

    sean_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("15:00"), to_minutes("15:30")),
        (to_minutes("16:00"), to_minutes("16:30")),
    ]

    lori_busy = [
        (to_minutes("10:00"), to_minutes("10:30")),
        (to_minutes("11:00"), to_minutes("13:00")),
        (to_minutes("15:30"), to_minutes("17:00")),
    ]

    start = Int("start")
    end = start + duration

    opt = Optimize()

    # Meeting within work hours
    opt.add(start >= work_start)
    opt.add(end <= work_end)

    # Optional: start time aligned to 30-minute slots
    opt.add(start % 30 == 0)

    # No overlap with any participant's busy times
    opt.add(no_overlap_constraints(start, duration, julie_busy))
    opt.add(no_overlap_constraints(start, duration, sean_busy))
    opt.add(no_overlap_constraints(start, duration, lori_busy))

    # Prefer the earliest feasible time
    opt.minimize(start)

    if opt.check() == sat:
        model = opt.model()
        s_val = model[start].as_long()
        e_val = s_val + duration
        print(day)
        print(f"{{{to_hhmm(s_val)}:{to_hhmm(e_val)}}}")
    else:
        print("No feasible time found.")

if __name__ == "__main__":
    main()