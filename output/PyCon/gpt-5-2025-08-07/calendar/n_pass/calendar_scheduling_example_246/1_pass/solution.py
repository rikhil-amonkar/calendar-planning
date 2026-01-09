from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

# Meeting parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Busy schedules (Monday)
schedules = {
    "Jacob":   [("13:30", "14:00"), ("14:30", "15:00")],
    "Diana":   [("09:30", "10:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "16:30")],
    "Adam":    [("09:30", "10:30"), ("11:00", "12:30"), ("15:30", "16:00")],
    "Angela":  [("09:30", "10:00"), ("10:30", "12:00"), ("13:00", "15:30"), ("16:00", "16:30")],
    "Dennis":  [("09:00", "09:30"), ("10:30", "11:30"), ("13:00", "15:00"), ("16:30", "17:00")],
}

# Convert schedules to minutes
busy_intervals = {}
for person, intervals in schedules.items():
    busy_intervals[person] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

# Candidate start times on 30-min grid within work hours
domain = list(range(work_start, work_end - duration + 1, 30))

def no_overlap(start):
    meeting_start = start
    meeting_end = start + duration
    # Check within work hours
    if meeting_start < work_start or meeting_end > work_end:
        return False
    # Check against all participants' busy intervals
    for intervals in busy_intervals.values():
        for bstart, bend in intervals:
            # Overlap if intervals intersect
            if meeting_start < bend and meeting_end > bstart:
                return False
    return True

# Set up CSP
problem = Problem()
problem.addVariable("start", domain)
problem.addConstraint(lambda s: no_overlap(s), ("start",))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose earliest feasible start
best = min(solutions, key=lambda sol: sol["start"])
start = best["start"]
end = start + duration

# Output in required format: {HH:MM:HH:MM} and day of the week
print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}} {day}")