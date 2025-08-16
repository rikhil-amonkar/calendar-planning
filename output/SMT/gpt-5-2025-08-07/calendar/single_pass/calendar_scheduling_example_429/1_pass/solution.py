# Requires: z3-solver package
# pip install z3-solver

from z3 import Int, Or, Optimize

def to_minutes(hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def schedule_meeting():
    # Problem specifics
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy intervals per participant as half-open ranges [start, end)
    busy = {
        "Judy":        [("13:00", "13:30"), ("16:00", "16:30")],
        "Olivia":      [("10:00", "10:30"), ("12:00", "13:00"), ("14:00", "14:30")],
        "Eric":        [],  # free entire day
        "Jacqueline":  [("10:00", "10:30"), ("15:00", "15:30")],
        "Laura":       [("09:00", "10:00"), ("10:30", "12:00"), ("13:00", "13:30"),
                        ("14:30", "15:00"), ("15:30", "17:00")],
        "Tyler":       [("09:00", "10:00"), ("11:00", "11:30"), ("12:30", "13:00"),
                        ("14:00", "14:30"), ("15:30", "17:00")],
        "Lisa":        [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
                        ("13:00", "13:30"), ("14:00", "14:30"), ("16:00", "17:00")],
    }

    # Convert times to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in busy.items()
    }

    # Z3 model
    start = Int("start")
    opt = Optimize()

    # Meeting within work hours
    opt.add(start >= work_start)
    opt.add(start + duration <= work_end)

    # Optional: align to 30-minute increments
    opt.add(start % 30 == 0)

    # Non-overlap constraints for each participant's busy intervals
    for intervals in busy_minutes.values():
        for s, e in intervals:
            # Meeting does not overlap [s, e)
            opt.add(Or(start + duration <= s, start >= e))

    # Prefer earliest feasible time
    opt.minimize(start)

    if opt.check().r == 1:  # sat
        model = opt.model()
        start_min = model[start].as_long()
        end_min = start_min + duration

        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {fmt_time(start_min)}")
        print(f"End Time: {fmt_time(end_min)}")
    else:
        raise RuntimeError("No feasible solution found, though one was expected.")

if __name__ == "__main__":
    schedule_meeting()