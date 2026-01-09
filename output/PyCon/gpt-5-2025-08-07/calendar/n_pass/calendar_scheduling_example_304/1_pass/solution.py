# Requires: python-constraint
from constraint import Problem

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Meeting parameters
DAY = "Monday"
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
DURATION = 30  # minutes

# Participants' busy schedules (on Monday)
busy = {
    "Christine": [("09:30", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Janice":    [],  # preference handled separately
    "Bobby":     [("12:00", "12:30"), ("14:30", "15:00")],
    "Elizabeth": [("09:00", "09:30"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Tyler":     [("09:00", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Edward":    [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
}

# Convert schedules to minutes
busy_minutes = {}
for person, intervals in busy.items():
    busy_minutes[person] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]

# Build domain of possible start times (every 30 minutes within work hours)
domain = list(range(WORK_START, WORK_END - DURATION + 1, 30))

problem = Problem()
problem.addVariable("start", domain)

# Constraint: must not overlap with any participant's busy times
def no_overlap_constraint_factory(person):
    intervals = busy_minutes[person]
    def constraint(start):
        for s, e in intervals:
            # overlap if [start, start+DURATION) intersects [s, e)
            if start < e and (start + DURATION) > s:
                return False
        return True
    return constraint

for person in busy_minutes:
    problem.addConstraint(no_overlap_constraint_factory(person), ("start",))

# Janice's preference: would rather not meet after 13:00 -> meeting should end by 13:00
JANICE_CUTOFF = time_to_minutes("13:00")
problem.addConstraint(lambda start: (start + DURATION) <= JANICE_CUTOFF, ("start",))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose the earliest feasible start time
best = min(solutions, key=lambda s: s["start"])
start = best["start"]
end = start + DURATION

start_str = minutes_to_time(start)
end_str = minutes_to_time(end)

# Output requirements:
# - Day of the week
# - Time range in HH:MM:HH:MM
# - Also include the braced format like {HH:MM:HH:MM}
print(DAY)
print(f"{start_str}:{end_str}")
print(f"{{{start_str}:{end_str}}}")