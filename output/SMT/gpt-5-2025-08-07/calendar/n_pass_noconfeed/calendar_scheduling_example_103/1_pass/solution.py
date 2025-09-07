from z3 import *

def parse_time(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Problem setup
    day = "Monday"
    day_start = parse_time("09:00")
    day_end   = parse_time("17:00")
    duration = 30  # minutes

    # Busy calendars (inclusive start, exclusive end)
    busy = {
        "Diane":   [("09:30","10:00"), ("14:30","15:00")],
        "Jack":    [("13:30","14:00"), ("14:30","15:00")],
        "Eugene":  [("09:00","10:00"), ("10:30","11:30"), ("12:00","14:30"), ("15:00","16:30")],
        "Patricia":[("09:30","10:30"), ("11:00","12:00"), ("12:30","14:00"), ("15:00","16:30")],
    }

    # Convert busy slots to minutes from midnight
    busy_minutes = {
        person: [(parse_time(s), parse_time(e)) for (s, e) in slots]
        for person, slots in busy.items()
    }

    # Z3 model
    s = Solver()
    start = Int("start")

    # Bounds: meeting fully within work hours
    s.add(start >= day_start)
    s.add(start + duration <= day_end)

    # No overlap with any busy interval for each participant
    for person, slots in busy_minutes.items():
        for (bs, be) in slots:
            # Meeting [start, start+duration) does not intersect busy [bs, be)
            s.add(Or(start >= be, start + duration <= bs))

    if s.check() != sat:
        print("No feasible meeting time found.")
        return

    m = s.model()
    start_time = m[start].as_long()
    end_time = start_time + duration

    out = f"{day} {{{fmt_time(start_time)}:{fmt_time(end_time)}}}"
    print(out)

if __name__ == "__main__":
    main()