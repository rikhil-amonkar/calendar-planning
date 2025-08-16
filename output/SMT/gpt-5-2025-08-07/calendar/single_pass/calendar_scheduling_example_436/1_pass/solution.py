from z3 import Solver, Int, Or

def hm_to_min(hm):
    h, m = map(int, hm.split(":"))
    return h * 60 + m

def min_to_hm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Problem parameters
    day = "Monday"
    work_start = hm_to_min("09:00")
    work_end = hm_to_min("17:00")
    duration = 30  # minutes

    # Existing schedules (busy intervals) in HH:MM
    schedules = {
        "Patrick": [("13:30", "14:00"), ("14:30", "15:00")],
        "Shirley": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("14:30", "15:00"), ("16:00", "17:00")],
        "Jeffrey": [("09:00", "09:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "17:00")],
        "Gloria":  [("11:30", "12:00"), ("15:00", "15:30")],
        "Nathan":  [("09:00", "09:30"), ("10:30", "12:00"), ("14:00", "17:00")],
        "Angela":  [("09:00", "09:30"), ("10:00", "11:00"), ("12:30", "15:00"), ("15:30", "16:30")],
        "David":   [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "14:00"), ("14:30", "16:30")],
    }

    # Convert schedules to minutes
    schedules_min = {
        person: [(hm_to_min(a), hm_to_min(b)) for a, b in intervals]
        for person, intervals in schedules.items()
    }

    # Candidate start times in 30-minute increments within work hours
    slots = list(range(work_start, work_end - duration + 1, 30))

    # Z3 model
    s = Int("start")
    solver = Solver()
    solver.add(Or([s == t for t in slots]))

    # No overlap with any busy interval for any participant:
    # For each busy [a, b), enforce: s >= b or s + duration <= a
    for intervals in schedules_min.values():
        for a, b in intervals:
            solver.add(Or(s >= b, s + duration <= a))

    if solver.check() != 1:  # sat
        raise RuntimeError("No solution found, but the problem statement guarantees one exists.")

    model = solver.model()
    start_min = model[s].as_long()
    end_min = start_min + duration

    # Output in required format
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {min_to_hm(start_min)} (24-hour format)")
    print(f"End Time: {min_to_hm(end_min)} (24-hour format)")

if __name__ == "__main__":
    main()