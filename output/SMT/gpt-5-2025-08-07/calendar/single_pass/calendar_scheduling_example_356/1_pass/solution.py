# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, Or

def to_minutes(hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return h * 60 + m

def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def schedule_meeting():
    # Work window (Monday)
    WORK_START = to_minutes("09:00")   # 540
    WORK_END   = to_minutes("17:00")   # 1020
    DURATION = 30

    # Busy intervals per participant (start, end) in minutes (half-open [start, end))
    schedules = {
        "Katherine": [(to_minutes("12:00"), to_minutes("12:30")),
                      (to_minutes("13:00"), to_minutes("14:30"))],
        "Rebecca":   [],  # no meetings
        "Julie":     [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("10:30"), to_minutes("11:00")),
                      (to_minutes("13:30"), to_minutes("14:00")),
                      (to_minutes("15:00"), to_minutes("15:30"))],
        "Angela":    [(to_minutes("09:00"), to_minutes("10:00")),
                      (to_minutes("10:30"), to_minutes("11:00")),
                      (to_minutes("11:30"), to_minutes("14:00")),
                      (to_minutes("14:30"), to_minutes("15:00")),
                      (to_minutes("16:30"), to_minutes("17:00"))],
        "Nicholas":  [(to_minutes("09:30"), to_minutes("11:00")),
                      (to_minutes("11:30"), to_minutes("13:30")),
                      (to_minutes("14:00"), to_minutes("16:00")),
                      (to_minutes("16:30"), to_minutes("17:00"))],
        "Carl":      [(to_minutes("09:00"), to_minutes("11:00")),
                      (to_minutes("11:30"), to_minutes("12:30")),
                      (to_minutes("13:00"), to_minutes("14:30")),
                      (to_minutes("15:00"), to_minutes("16:00")),
                      (to_minutes("16:30"), to_minutes("17:00"))],
    }

    # Preference: Angela would like to avoid more meetings before 15:00
    PREFERRED_START = to_minutes("15:00")

    opt = Optimize()
    start = Int("start")
    end = start + DURATION

    # Hard constraints: within work hours
    opt.add(start >= WORK_START)
    opt.add(end <= WORK_END)

    # Hard constraints: no overlap with any busy interval for any participant
    for person, intervals in schedules.items():
        for (b_start, b_end) in intervals:
            opt.add(Or(end <= b_start, start >= b_end))

    # Soft preference: start at or after 15:00 if possible
    opt.add_soft(start >= PREFERRED_START, weight=1, id="after_3pm")

    # Tie-breaker: choose the earliest feasible start time
    opt.minimize(start)

    if opt.check() != 1:  # sat
        raise RuntimeError("No feasible meeting time found.")

    m = opt.model()
    s = m.evaluate(start).as_long()
    e = s + DURATION

    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {minutes_to_hhmm(s)}")
    print(f"End Time: {minutes_to_hhmm(e)}")

if __name__ == "__main__":
    schedule_meeting()