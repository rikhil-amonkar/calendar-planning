# Requires: pip install z3-solver
from z3 import Optimize, Int, Or, sat

def to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def fmt_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def add_no_overlap(o, start, end, intervals):
    # For each busy interval [s,e), enforce meeting does not overlap: end <= s or start >= e
    for (s, e) in intervals:
        o.add(Or(end <= s, start >= e))

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end   = to_minutes("17:00")
    duration = 30  # minutes

    # Participants' busy intervals on Monday (all times [start, end) in minutes)
    busy = {
        "Ronald":   [],
        "Stephen":  [(to_minutes("10:00"), to_minutes("10:30")),
                     (to_minutes("12:00"), to_minutes("12:30"))],
        "Brittany": [(to_minutes("11:00"), to_minutes("11:30")),
                     (to_minutes("13:30"), to_minutes("14:00")),
                     (to_minutes("15:30"), to_minutes("16:00")),
                     (to_minutes("16:30"), to_minutes("17:00"))],
        "Dorothy":  [(to_minutes("09:00"), to_minutes("09:30")),
                     (to_minutes("10:00"), to_minutes("10:30")),
                     (to_minutes("11:00"), to_minutes("12:30")),
                     (to_minutes("13:00"), to_minutes("15:00")),
                     (to_minutes("15:30"), to_minutes("17:00"))],
        "Rebecca":  [(to_minutes("09:30"), to_minutes("10:30")),
                     (to_minutes("11:00"), to_minutes("11:30")),
                     (to_minutes("12:00"), to_minutes("12:30")),
                     (to_minutes("13:00"), to_minutes("17:00"))],
        "Jordan":   [(to_minutes("09:00"), to_minutes("09:30")),
                     (to_minutes("10:00"), to_minutes("11:00")),
                     (to_minutes("11:30"), to_minutes("12:00")),
                     (to_minutes("13:00"), to_minutes("15:00")),
                     (to_minutes("15:30"), to_minutes("16:30"))],
    }

    o = Optimize()
    start = Int("start")
    end = Int("end")

    # Meeting duration and working hours
    o.add(end == start + duration)
    o.add(start >= work_start, end <= work_end)

    # Optional: align meeting start to 30-minute increments
    o.add((start - work_start) % 30 == 0)

    # No-overlap constraints for each participant
    for person, intervals in busy.items():
        add_no_overlap(o, start, end, intervals)

    # Prefer earliest feasible time
    o.minimize(start)

    if o.check() == sat:
        m = o.model()
        s = m[start].as_long()
        e = m[end].as_long()
        time_range = f"{{{fmt_time(s)}:{fmt_time(e)}}}"
        print(day)
        print(time_range)
    else:
        print(day)
        print("{No feasible 30-minute slot found}")

if __name__ == "__main__":
    main()