# Requires: python-constraint
from constraint import Problem

def parse_time(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    return f"{minutes//60:02d}:{minutes%60:02d}"

# Meeting parameters
day = "Monday"
meeting_duration = 30  # minutes
work_start = parse_time("09:00")
work_end = parse_time("17:00")

# Busy schedules (Monday)
busy_intervals = {
    "Jose":   [("11:00","11:30"), ("12:30","13:00")],
    "Keith":  [("14:00","14:30"), ("15:00","15:30")],
    "Logan":  [("09:00","10:00"), ("12:00","12:30"), ("15:00","15:30")],
    "Megan":  [("09:00","10:30"), ("11:00","12:00"), ("13:00","13:30"), ("14:30","16:30")],
    "Gary":   [("09:00","09:30"), ("10:00","10:30"), ("11:30","13:00"), ("13:30","14:00"), ("14:30","16:30")],
    "Bobby":  [("11:00","11:30"), ("12:00","12:30"), ("13:00","16:00")],
}

# Convert all busy intervals to minutes
all_busy = []
for person, intervals in busy_intervals.items():
    for s, e in intervals:
        all_busy.append((parse_time(s), parse_time(e)))

problem = Problem()

# Candidate meeting start times (every 30 minutes within work hours)
domain = list(range(work_start, work_end - meeting_duration + 1, 30))
problem.addVariable("start", domain)

# No overlap with any busy interval (use half-open intervals [start, end))
for bs, be in all_busy:
    problem.addConstraint(lambda s, bs=bs, be=be: not (s < be and (s + meeting_duration) > bs), ("start",))

# Preference: Jose does not want to meet after 15:30 (meeting can start at or before 15:30)
problem.addConstraint(lambda s: s <= parse_time("15:30"), ("start",))

# Get solutions and pick the earliest valid start
solutions = problem.getSolutions()
if not solutions:
    raise RuntimeError("No valid meeting time found, but a solution was expected.")

best_start = min(solutions, key=lambda sol: sol["start"])["start"]
best_end = best_start + meeting_duration

# Output: time range in {HH:MM:HH:MM} and the day of week
print(f"{{{fmt_time(best_start)}:{fmt_time(best_end)}}}")
print(day)