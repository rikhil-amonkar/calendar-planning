# Requires: python-constraint
from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    return f"{minutes//60:02d}:{minutes%60:02d}"

def intervals_to_minutes(intervals):
    return [(to_minutes(s), to_minutes(e)) for s, e in intervals]

def is_free(blocks, start, duration):
    end = start + duration
    for b_start, b_end in blocks:
        # Overlap if intervals intersect: [start,end) with [b_start,b_end)
        if start < b_end and end > b_start:
            return False
    return True

# Meeting details
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' blocked intervals (inclusive start, exclusive end)
gregory_blocks = intervals_to_minutes([
    ("09:00", "10:00"),
    ("10:30", "11:30"),
    ("12:30", "13:00"),
    ("13:30", "14:00"),
])

natalie_blocks = intervals_to_minutes([
    # wide open (no blocks)
])

christine_blocks = intervals_to_minutes([
    ("09:00", "11:30"),
    ("13:30", "17:00"),
])

vincent_blocks = intervals_to_minutes([
    ("09:00", "09:30"),
    ("10:30", "12:00"),
    ("12:30", "14:00"),
    ("14:30", "17:00"),
])

problem = Problem()

# Candidate start times on 30-minute grid within work hours
domain = list(range(work_start, work_end - duration + 1, 30))
problem.addVariable("start", domain)

def availability_constraint(start):
    return (
        is_free(gregory_blocks, start, duration) and
        is_free(natalie_blocks, start, duration) and
        is_free(christine_blocks, start, duration) and
        is_free(vincent_blocks, start, duration)
    )

problem.addConstraint(availability_constraint, ("start",))

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No feasible meeting time found (but one was expected).")

# Choose the earliest feasible start
best_start = min(s["start"] for s in solutions)
best_end = best_start + duration

time_range = f"{to_hhmm(best_start)}:{to_hhmm(best_end)}"

# Output requirements:
# - Print the time in HH:MM:HH:MM format
# - Print the day of the week
# - Ensure output includes the time range wrapped in braces as well
print(time_range)
print(day)
print("{" + time_range + "}")