from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' busy schedules (inclusive of start, exclusive of end)
busy = {
    "Emily": [("10:00", "10:30"), ("16:00", "16:30")],
    "Mason": [],
    "Maria": [("10:30", "11:00"), ("14:00", "14:30")],
    "Carl": [("09:30", "10:00"), ("10:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
    "David": [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "15:00"), ("16:00", "17:00")],
    "Frank": [("09:30", "10:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:30", "17:00")],
}

# Convert busy intervals to minutes
busy_min = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for person, intervals in busy.items()
}

# Set up CSP
problem = Problem()

# Domain: all valid half-hour start times within work hours
domain = list(range(work_start, work_end - duration + 1, 30))
problem.addVariable("start", domain)

# For each busy interval of every participant, ensure no overlap
for person, intervals in busy_min.items():
    for (bs, be) in intervals:
        # Meeting [start, start+duration) must not overlap with [bs, be)
        problem.addConstraint(lambda s, bs=bs, be=be: (s + duration) <= bs or s >= be, ("start",))

solutions = problem.getSolutions()
if not solutions:
    raise RuntimeError("No feasible meeting time found, but one was expected.")

# Choose the earliest feasible time
best_start = min(sol["start"] for sol in solutions)
best_end = best_start + duration

# Output in the required format: include day and {HH:MM:HH:MM}
print(f"{day} {{{to_hhmm(best_start)}:{to_hhmm(best_end)}}}")