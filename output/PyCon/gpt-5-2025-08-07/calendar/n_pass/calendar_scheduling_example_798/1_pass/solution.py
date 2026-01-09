from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(mins):
    return f"{mins // 60:02d}:{mins % 60:02d}"

# Meeting parameters
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes
days = ["Monday", "Tuesday", "Wednesday"]
day_order = {d: i for i, d in enumerate(days)}

# Participants' busy schedules
raw_schedules = {
    "Nancy": {
        "Monday": [("10:00", "10:30"), ("11:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Tuesday": [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00")],
        "Wednesday": [("10:00", "11:30"), ("13:30", "16:00")],
    },
    "Jose": {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:00", "17:00")],
        "Wednesday": [("09:00", "09:30"), ("10:00", "12:30"), ("13:30", "14:30"), ("15:00", "17:00")],
    }
}

# Convert schedules to minutes
schedules = {}
for person, day_map in raw_schedules.items():
    schedules[person] = {}
    for day in days:
        intervals = day_map.get(day, [])
        schedules[person][day] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

def is_available(day, start):
    end = start + duration
    # Check within work hours
    if not (work_start <= start and end <= work_end):
        return False
    # Check all participants' busy intervals
    for person in schedules:
        for (b_start, b_end) in schedules[person].get(day, []):
            if max(start, b_start) < min(end, b_end):  # overlap
                return False
    return True

# Build CSP
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", list(range(work_start, work_end - duration + 1, 30)))

def availability_constraint(day, start):
    return is_available(day, start)

problem.addConstraint(availability_constraint, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Pick earliest by day then time
best = min(solutions, key=lambda s: (day_order[s["day"]], s["start"]))
best_day = best["day"]
best_start = best["start"]
best_end = best_start + duration

# Output: include both time range in {HH:MM:HH:MM} and the day of the week
print(f"{best_day} {{{fmt_time(best_start)}:{fmt_time(best_end)}}}")