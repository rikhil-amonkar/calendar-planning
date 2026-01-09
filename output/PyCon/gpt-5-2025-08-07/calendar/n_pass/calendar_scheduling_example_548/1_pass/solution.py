# Requires: python-constraint
from constraint import Problem

# Time helpers
def to_minutes(h, m=0):
    return h * 60 + m

def minutes_to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

def overlaps(s1, e1, s2, e2):
    return max(s1, s2) < min(e1, e2)

# Meeting setup
day = "Monday"
work_start = to_minutes(9, 0)
work_end = to_minutes(17, 0)
duration = 30  # minutes

# Participants' schedules (busy intervals) in minutes from midnight
judy_busy = []  # Judy is free the entire day
nicole_busy = [
    (to_minutes(9, 0), to_minutes(10, 0)),
    (to_minutes(10, 30), to_minutes(16, 30)),
]

# Preference: Nicole would rather not meet before 16:00 (treat as constraint)
nicole_preferred_earliest = to_minutes(16, 0)

# Build the problem
problem = Problem()

# Possible start times at 30-minute increments within work hours
starts = []
t = work_start
while t + duration <= work_end:
    # 30-minute grid
    if t % 30 == 0:
        starts.append(t)
    t += 30

problem.addVariable("start", starts)

# Constraints: within work hours
problem.addConstraint(lambda s: work_start <= s and s + duration <= work_end, ("start",))

# Constraints: participants' availability (no overlap with busy intervals)
def availability_constraint(s):
    e = s + duration
    # Judy
    for bs, be in []:  # judy_busy is empty
        if overlaps(s, e, bs, be):
            return False
    # Nicole
    for bs, be in nicole_busy:
        if overlaps(s, e, bs, be):
            return False
    return True

problem.addConstraint(availability_constraint, ("start",))

# Preference: not before 16:00
problem.addConstraint(lambda s: s >= nicole_preferred_earliest, ("start",))

solution = problem.getSolution()
if not solution:
    raise RuntimeError("No feasible meeting time found, but one was expected.")

start = solution["start"]
end = start + duration
start_str = minutes_to_hhmm(start)
end_str = minutes_to_hhmm(end)

# Output format:
# 1) Time range in braces: {HH:MM:HH:MM}
# 2) Day of the week on next line
print(f"{{{start_str}:{end_str}}}")
print(day)