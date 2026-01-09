from constraint import Problem

def minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m//60:02d}:{m%60:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    return max(a_start, b_start) < min(a_end, b_end)

# Settings
DAY = "Monday"
WORK_START = minutes("09:00")
WORK_END = minutes("17:00")
DURATION = 30  # minutes

# Busy schedules (inclusive of start, exclusive of end)
eric_busy = [
    (minutes("12:00"), minutes("13:00")),
    (minutes("14:00"), minutes("15:00")),
]

henry_busy = [
    (minutes("09:30"), minutes("10:00")),
    (minutes("10:30"), minutes("11:00")),
    (minutes("11:30"), minutes("12:30")),
    (minutes("13:00"), minutes("13:30")),
    (minutes("14:30"), minutes("15:00")),
    (minutes("16:00"), minutes("17:00")),
]

# Build problem
problem = Problem()
# Start times on 30-minute boundaries within work hours ensuring full duration fits
domain = list(range(WORK_START, WORK_END - DURATION + 1, 30))
problem.addVariable("start", domain)

def availability_constraint(start):
    end = start + DURATION
    # Within work hours
    if not (WORK_START <= start and end <= WORK_END):
        return False
    # Check Eric's and Henry's busy times
    for bs, be in eric_busy + henry_busy:
        if overlaps(start, end, bs, be):
            return False
    return True

problem.addConstraint(availability_constraint, ["start"])

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No feasible meeting time found.")

# Preference: Henry would rather not meet after 10:00 (i.e., prefer start <= 10:00)
PREF_CUTOFF = minutes("10:00")
preferred = [s for s in solutions if s["start"] <= PREF_CUTOFF]

candidates = preferred if preferred else solutions
best = min(candidates, key=lambda s: s["start"])
start = best["start"]
end = start + DURATION

# Output
print(DAY)
print(f"{{{fmt(start)}:{fmt(end)}}}")