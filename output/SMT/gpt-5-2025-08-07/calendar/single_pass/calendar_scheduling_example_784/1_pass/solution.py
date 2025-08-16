from z3 import *

def minutes(hh_mm):
    hh, mm = map(int, hh_mm.split(":"))
    return hh * 60 + mm

def fmt_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

def main():
    # Days mapping
    days = {"Monday": 0, "Tuesday": 1, "Wednesday": 2}
    day_names = {v: k for k, v in days.items()}

    # Work hours and meeting duration
    WORK_START = minutes("09:00")
    WORK_END = minutes("17:00")
    DURATION = 60

    # Blocked intervals per participant per day
    blocked = {
        "Judith": {
            "Monday":    [(minutes("12:00"), minutes("12:30"))],
            "Tuesday":   [],
            "Wednesday": [(minutes("11:30"), minutes("12:00"))],
        },
        "Timothy": {
            "Monday": [
                (minutes("09:30"), minutes("10:00")),
                (minutes("10:30"), minutes("11:30")),
                (minutes("12:30"), minutes("14:00")),
                (minutes("15:30"), minutes("17:00")),
            ],
            "Tuesday": [
                (minutes("09:30"), minutes("13:00")),
                (minutes("13:30"), minutes("14:00")),
                (minutes("14:30"), minutes("17:00")),
            ],
            "Wednesday": [
                (minutes("09:00"), minutes("09:30")),
                (minutes("10:30"), minutes("11:00")),
                (minutes("13:30"), minutes("14:30")),
                (minutes("15:00"), minutes("15:30")),
                (minutes("16:00"), minutes("16:30")),
            ],
        },
    }

    # Z3 variables
    D = Int("D")        # Day index
    S = Int("S")        # Start time in minutes from 00:00
    E = Int("E")        # End time in minutes from 00:00

    o = Optimize()

    # Day domain: Monday, Tuesday, Wednesday
    o.add(Or(D == days["Monday"], D == days["Tuesday"], D == days["Wednesday"]))

    # Meeting duration and within work hours
    o.add(E == S + DURATION)
    o.add(S >= WORK_START)
    o.add(E <= WORK_END)

    # No overlap with blocked intervals for each participant on the chosen day
    for person, schedule in blocked.items():
        for day_name, intervals in schedule.items():
            d_idx = days[day_name]
            for (bs, be) in intervals:
                # If chosen day == this day, enforce non-overlap: E <= bs or S >= be
                o.add(Implies(D == d_idx, Or(E <= bs, S >= be)))

    # Preferences (soft constraints):
    # - Judith would like to avoid Monday
    o.add_soft(D != days["Monday"])
    # - Judith would like to avoid Wednesday before 12:00
    o.add_soft(Or(D != days["Wednesday"], S >= minutes("12:00")))

    # Tie-breaker: earliest feasible start time
    o.minimize(S)

    if o.check() != sat:
        raise RuntimeError("No feasible schedule found, but the problem statement guarantees one.")

    m = o.model()
    day_idx = m[D].as_long()
    start = m[S].as_long()
    end = m[E].as_long()

    # Output in the required format
    print("SOLUTION:")
    print(f"Day: {day_names[day_idx]}")
    print(f"Start Time: {fmt_time(start)}")
    print(f"End Time: {fmt_time(end)}")

if __name__ == "__main__":
    main()