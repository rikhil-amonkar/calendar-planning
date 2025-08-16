# Requires: z3-solver
from z3 import Int, Or, Optimize

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def main():
    # Work hours and meeting duration
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules (half-open intervals [start, end))
    busy = {
        "Andrea": [("09:30","10:30"), ("13:30","14:30")],
        "Ruth":   [("12:30","13:00"), ("15:00","15:30")],
        "Steven": [("10:00","10:30"), ("11:00","11:30"), ("12:00","12:30"), ("13:30","14:00"), ("15:00","16:00")],
        "Grace":  [],
        "Kyle":   [("09:00","09:30"), ("10:30","12:00"), ("12:30","13:00"), ("13:30","15:00"), ("15:30","16:00"), ("16:30","17:00")],
        "Elijah": [("09:00","11:00"), ("11:30","13:00"), ("13:30","14:00"), ("15:30","16:00"), ("16:30","17:00")],
        "Lori":   [("09:00","09:30"), ("10:00","11:30"), ("12:00","13:30"), ("14:00","16:00"), ("16:30","17:00")],
    }

    # Convert to minutes
    busy_min = {
        p: [(to_minutes(s), to_minutes(e)) for (s, e) in intervals]
        for p, intervals in busy.items()
    }

    # Z3 variables and optimizer (to get the earliest valid meeting)
    t = Int("t")  # start time in minutes since 00:00
    opt = Optimize()

    # Within work hours
    opt.add(t >= work_start)
    opt.add(t + duration <= work_end)

    # Align to 30-minute boundaries (optional but typical for meetings)
    opt.add((t - work_start) % 30 == 0)

    # No overlap with any busy interval of any participant
    for p, intervals in busy_min.items():
        for (s, e) in intervals:
            # Ensure [t, t+duration) does not overlap [s, e)
            opt.add(Or(t + duration <= s, t >= e))

    # Minimize start time for a deterministic earliest slot
    opt.minimize(t)

    if opt.check() != 1:  # sat
        raise RuntimeError("No feasible meeting time found, but problem states a solution exists.")

    model = opt.model()
    start = model.eval(t).as_long()
    end = start + duration

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_minutes(start)} (24-hour format)")
    print(f"End Time: {fmt_minutes(end)} (24-hour format)")

if __name__ == "__main__":
    main()