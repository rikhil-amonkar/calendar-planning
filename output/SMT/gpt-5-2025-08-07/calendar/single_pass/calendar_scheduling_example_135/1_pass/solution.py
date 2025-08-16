from z3 import Optimize, Int, Or, And, sat

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Problem data
    day = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules (inclusive of start, exclusive of end)
    schedules = {
        "Eric": [],
        "Ashley": [("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00")],
        "Ronald": [("09:00", "09:30"), ("10:00", "11:30"), ("12:30", "14:00"), ("14:30", "17:00")],
        "Larry": [("09:00", "12:00"), ("13:00", "17:00")],
    }

    # Convert to minutes
    busy_minutes = {
        person: [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Z3 variables
    start = Int("start")
    end = Int("end")

    opt = Optimize()
    opt.add(end == start + duration)
    opt.add(start >= work_start, end <= work_end)

    # Optional: keep starts on 5-minute boundaries (typical calendars). Not required, but harmless.
    # opt.add(start % 5 == 0)

    # No overlap with any busy interval for any participant
    for person, intervals in busy_minutes.items():
        for (bs, be) in intervals:
            # Meeting [start, end) does not overlap [bs, be) -> end <= bs or start >= be
            opt.add(Or(end <= bs, start >= be))

    # Prefer earliest feasible time
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible schedule found, but problem statement guarantees one.")

    model = opt.model()
    start_time = model[start].as_long()
    end_time = model[end].as_long()

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_time_str(start_time)}")
    print(f"End Time: {minutes_to_time_str(end_time)}")

if __name__ == "__main__":
    main()