from z3 import Optimize, Int, Or, And

def to_minutes(t):
    # t format: "HH:MM" 24-hour
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Problem setup
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules (all on Monday)
    busy = {
        "Christine": [("09:30","10:30"), ("12:00","12:30"), ("13:00","13:30"), ("14:30","15:00"), ("16:00","16:30")],
        "Janice":    [],  # Open all day
        "Bobby":     [("12:00","12:30"), ("14:30","15:00")],
        "Elizabeth": [("09:00","09:30"), ("11:30","13:00"), ("13:30","14:00"), ("15:00","15:30"), ("16:00","17:00")],
        "Tyler":     [("09:00","11:00"), ("12:00","12:30"), ("13:00","13:30"), ("15:30","16:00"), ("16:30","17:00")],
        "Edward":    [("09:00","09:30"), ("10:00","11:00"), ("11:30","14:00"), ("14:30","15:30"), ("16:00","17:00")],
    }

    # Convert to absolute minutes
    busy_minutes = {
        p: [(to_minutes(s), to_minutes(e)) for (s, e) in intervals]
        for p, intervals in busy.items()
    }

    # Z3 model
    opt = Optimize()
    s = Int("start")

    # Basic constraints: within work hours and on 30-minute boundaries
    opt.add(s >= work_start)
    opt.add(s + duration <= work_end)
    opt.add(s % 30 == 0)

    # No overlap with any participant's busy times
    for person, intervals in busy_minutes.items():
        for (bs, be) in intervals:
            # Meeting [s, s+dur) does not overlap [bs, be)
            opt.add(Or(s + duration <= bs, s >= be))

    # Preference: Janice would rather not meet after 13:00 (prefer start <= 13:00)
    thirteen = to_minutes("13:00")
    opt.add_soft(s <= thirteen, weight="1", id="janice_pref")

    # Also prefer the earliest feasible time
    opt.minimize(s)

    if opt.check() !=  sat:
        raise RuntimeError("No feasible schedule found, but the problem statement guarantees a solution.")

    m = opt.model()
    start_time = m[s].as_long()
    end_time = start_time + duration

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {to_hhmm(start_time)}")
    print(f"End Time: {to_hhmm(end_time)}")

if __name__ == "__main__":
    main()