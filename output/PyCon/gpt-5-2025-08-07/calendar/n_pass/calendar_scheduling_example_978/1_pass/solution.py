# Requires: python-constraint (pip install python-constraint)
from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Busy schedules
brian_busy = {
    "Monday":    [("09:30","10:00"), ("12:30","14:30"), ("15:30","16:00")],
    "Tuesday":   [("09:00","09:30")],
    "Wednesday": [("12:30","14:00"), ("16:30","17:00")],
    "Thursday":  [("11:00","11:30"), ("13:00","13:30"), ("16:30","17:00")],
    "Friday":    [("09:30","10:00"), ("10:30","11:00"), ("13:00","13:30"),
                  ("15:00","16:00"), ("16:30","17:00")],
}

julia_busy = {
    "Monday":    [("09:00","10:00"), ("11:00","11:30"), ("12:30","13:00"), ("15:30","16:00")],
    "Tuesday":   [("13:00","14:00"), ("16:00","16:30")],
    "Wednesday": [("09:00","11:30"), ("12:00","12:30"), ("13:00","17:00")],
    "Thursday":  [("09:00","10:30"), ("11:00","17:00")],
    "Friday":    [("09:00","10:00"), ("10:30","11:30"), ("12:30","14:00"),
                  ("14:30","15:00"), ("15:30","16:00")],
}

# Convert busy schedules to minutes for easy comparison
def convert_busy(busy_dict):
    out = {}
    for day, slots in busy_dict.items():
        out[day] = [(to_minutes(s), to_minutes(e)) for s, e in slots]
    return out

brian_busy_m = convert_busy(brian_busy)
julia_busy_m = convert_busy(julia_busy)

work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 60  # minutes
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Build problem
problem = Problem()
problem.addVariable("day", days)
# Start times every 30 minutes within working hours so that end time <= 17:00
start_times = list(range(work_start, work_end - duration + 1, 30))
problem.addVariable("start", start_times)

def no_overlap(meet_start, meet_end, busy_list):
    for bs, be in busy_list:
        # overlap if intervals intersect with positive length
        if max(meet_start, bs) < min(meet_end, be):
            return False
    return True

def availability_constraint(day, start):
    end = start + duration
    # Within work hours
    if end > work_end:
        return False
    # Check both participants
    if not no_overlap(start, end, brian_busy_m.get(day, [])):
        return False
    if not no_overlap(start, end, julia_busy_m.get(day, [])):
        return False
    return True

problem.addConstraint(availability_constraint, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    print("No feasible solution found.")
else:
    # Preference: avoid Monday if any non-Monday solution exists
    non_monday = [s for s in solutions if s["day"] != "Monday"]
    candidates = non_monday if non_monday else solutions

    day_order = {d: i for i, d in enumerate(days)}  # Monday..Friday
    best = sorted(candidates, key=lambda s: (day_order[s["day"]], s["start"]))[0]

    start = best["start"]
    end = start + duration
    day = best["day"]

    start_str = to_hhmm(start)
    end_str = to_hhmm(end)

    # Output must include both the day and the time range in HH:MM:HH:MM format with braces
    print(f"{day} {{{start_str}:{end_str}}}")