# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m//60:02d}:{m%60:02d}"

# Meeting details
DAY = "Monday"
MEETING_DURATION = 30  # minutes
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")

# Participants' busy schedules for Monday (half-open intervals [start, end))
busy = {
    "Tyler": [],
    "Kelly": [],
    "Stephanie": [("11:00", "11:30"), ("14:30", "15:00")],
    "Hannah": [],
    "Joe": [("09:00", "09:30"), ("10:00", "12:00"), ("12:30", "13:00"), ("14:00", "17:00")],
    "Diana": [("09:00", "10:30"), ("11:30", "12:00"), ("13:00", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
    "Deborah": [("09:00", "10:00"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "16:30")],
}

# Convert busy windows to minutes
busy_minutes = {}
for person, intervals in busy.items():
    busy_minutes[person] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

# Build the problem
problem = Problem()

# Possible start times: every 30 minutes within work hours, ensuring meeting ends by WORK_END
domain = list(range(WORK_START, WORK_END - MEETING_DURATION + 1, 30))
problem.addVariable("start", domain)

# Add constraints: meeting must not overlap any busy interval for any participant
for person, intervals in busy_minutes.items():
    for (bs, be) in intervals:
        # No overlap condition for half-open intervals: [s, s+dur) and [bs, be)
        # Allowed if s+dur <= bs or s >= be
        problem.addConstraint(lambda s, bs=bs, be=be: (s + MEETING_DURATION) <= bs or s >= be, ("start",))

# Find all feasible start times and choose the earliest
solutions = problem.getSolutions()
if not solutions:
    raise SystemExit("No feasible meeting time found.")

best = min(solutions, key=lambda sol: sol["start"])
start = best["start"]
end = start + MEETING_DURATION

start_str = fmt(start)
end_str = fmt(end)

# Output:
# 1) HH:MM:HH:MM
# 2) Day of the week
# 3) Curly-braced time range {HH:MM:HH:MM}
print(f"{start_str}:{end_str}")
print(DAY)
print(f"{{{start_str}:{end_str}}}")