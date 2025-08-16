from z3 import *

def to_minutes(hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Days mapping
    days = ["Monday", "Tuesday", "Wednesday"]
    day_idx = {d: i for i, d in enumerate(days)}

    # Meeting duration in minutes
    duration = 60

    # Work hours: 09:00 to 17:00
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")

    # Blocked intervals per participant per day (minutes since midnight)
    # Martha
    martha = {
        day_idx["Monday"]: [(to_minutes("16:00"), to_minutes("17:00"))],
        day_idx["Tuesday"]: [(to_minutes("15:00"), to_minutes("15:30"))],
        day_idx["Wednesday"]: [
            (to_minutes("10:00"), to_minutes("11:00")),
            (to_minutes("14:00"), to_minutes("14:30")),
        ],
    }

    # Beverly
    beverly = {
        day_idx["Monday"]: [
            (to_minutes("09:00"), to_minutes("13:30")),
            (to_minutes("14:00"), to_minutes("17:00")),
        ],
        day_idx["Tuesday"]: [(to_minutes("09:00"), to_minutes("17:00"))],
        day_idx["Wednesday"]: [
            (to_minutes("09:30"), to_minutes("15:30")),
            (to_minutes("16:30"), to_minutes("17:00")),
        ],
    }

    # Z3 variables
    day = Int("day")       # 0 = Monday, 1 = Tuesday, 2 = Wednesday
    start = Int("start")   # minutes since midnight
    end = Int("end")       # minutes since midnight

    s = Solver()

    # Domain constraints
    s.add(day >= 0, day <= 2)
    s.add(end == start + duration)
    s.add(start >= work_start, end <= work_end)

    # Non-overlap constraints for Martha
    for d, intervals in martha.items():
        for (bs, be) in intervals:
            # If meeting is on day d, it must not overlap [bs, be)
            s.add(Implies(day == d, Or(end <= bs, start >= be)))

    # Non-overlap constraints for Beverly
    for d, intervals in beverly.items():
        for (bs, be) in intervals:
            s.add(Implies(day == d, Or(end <= bs, start >= be)))

    if s.check() != sat:
        raise RuntimeError("No solution found, but one was expected.")

    m = s.model()
    chosen_day = days[m[day].as_long()]
    start_time = to_hhmm(m[start].as_long())
    end_time = to_hhmm(m[end].as_long())

    print("SOLUTION:")
    print(f"Day: {chosen_day}")
    print(f"Start Time: {start_time} (24-hour format)")
    print(f"End Time: {end_time} (24-hour format)")

if __name__ == "__main__":
    main()