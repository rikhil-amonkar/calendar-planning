# Requires: z3-solver (pip install z3-solver)
from z3 import Optimize, Int, And, Or, sat

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Workday and meeting parameters
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules as absolute minutes from midnight
    schedules = {
        "Joan":    [("11:30", "12:00"), ("14:30", "15:00")],
        "Megan":   [("09:00", "10:00"), ("14:00", "14:30"), ("16:00", "16:30")],
        "Austin":  [],
        "Betty":   [("09:30", "10:00"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:00", "16:30")],
        "Judith":  [("09:00", "11:00"), ("12:00", "13:00"), ("14:00", "15:00")],
        "Terry":   [("09:30", "10:00"), ("11:30", "12:30"), ("13:00", "14:00"),
                    ("15:00", "15:30"), ("16:00", "17:00")],
        "Kathryn": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "13:00"),
                    ("14:00", "16:00"), ("16:30", "17:00")],
    }

    # Convert to absolute minute intervals
    busy = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Decision variable: start time in absolute minutes since midnight
    # Constrain to fit fully within work hours
    opt = Optimize()
    start = Int("start")
    opt.add(And(start >= work_start, start + duration <= work_end))

    # For each participant, ensure the meeting does not overlap any busy block
    for person, intervals in busy.items():
        for (bs, be) in intervals:
            # Non-overlap: [start, start+dur) ∩ [bs, be) = ∅
            opt.add(Or(start + duration <= bs, start >= be))

    # Prefer the earliest feasible start
    opt.minimize(start)

    if opt.check() != sat:
        raise RuntimeError("No feasible meeting time found, but a solution was expected.")

    model = opt.model()
    start_abs = model[start].as_long()
    end_abs = start_abs + duration

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_hhmm(start_abs)}")
    print(f"End Time: {fmt_hhmm(end_abs)}")

if __name__ == "__main__":
    main()