# Requires: python-constraint
from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting settings
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' busy schedules on Monday (start, end) in minutes since midnight
jack_busy = [
    (to_minutes("09:30"), to_minutes("10:30")),
    (to_minutes("11:00"), to_minutes("11:30")),
    (to_minutes("12:30"), to_minutes("13:00")),
    (to_minutes("14:00"), to_minutes("14:30")),
    (to_minutes("16:00"), to_minutes("16:30")),
]

charlotte_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("12:00")),
    (to_minutes("12:30"), to_minutes("13:30")),
    (to_minutes("14:00"), to_minutes("16:00")),
]

# Jack would like to avoid meetings after 12:30 (treat as a hard constraint here)
jack_pref_end_by = to_minutes("12:30")

# Domain: possible start times on 30-minute boundaries within work hours
domain = [t for t in range(work_start, work_end - duration + 1, 30)]

problem = Problem()
problem.addVariable("start", domain)

# Must end within work hours
problem.addConstraint(lambda s: s + duration <= work_end, ["start"])

# Honor Jack's preference to avoid meetings after 12:30
problem.addConstraint(lambda s: s + duration <= jack_pref_end_by, ["start"])

# No overlap with Jack's busy times
for s_b, e_b in jack_busy:
    problem.addConstraint(lambda s, sb=s_b, eb=e_b: not (s < eb and s + duration > sb), ["start"])

# No overlap with Charlotte's busy times
for s_b, e_b in charlotte_busy:
    problem.addConstraint(lambda s, sb=s_b, eb=e_b: not (s < eb and s + duration > sb), ["start"])

solutions = problem.getSolutions()
if not solutions:
    raise RuntimeError("No feasible meeting time found.")

# Choose the earliest feasible start time
best_start = min(sol["start"] for sol in solutions)
best_end = best_start + duration

time_range = f"{to_hhmm(best_start)}:{to_hhmm(best_end)}"

# Output as required
print("{" + time_range + "}")
print(day)