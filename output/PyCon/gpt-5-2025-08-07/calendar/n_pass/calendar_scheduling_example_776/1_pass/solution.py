# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

# Time utilities
def to_minutes(h, m):
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours and meeting duration
WORK_START = to_minutes(9, 0)
WORK_END = to_minutes(17, 0)
DURATION = 30

# Generate all 30-minute start times within work hours
all_starts = list(range(WORK_START, WORK_END - DURATION + 1, 30))

# Jennifer's busy schedules (minutes since midnight)
busy_jennifer = {
    "Monday": [
        (to_minutes(9, 0),  to_minutes(11, 0)),
        (to_minutes(11, 30), to_minutes(13, 0)),
        (to_minutes(13, 30), to_minutes(14, 30)),
        (to_minutes(15, 0),  to_minutes(17, 0)),
    ],
    "Tuesday": [
        (to_minutes(9, 0),  to_minutes(11, 30)),
        (to_minutes(12, 0), to_minutes(17, 0)),
    ],
    "Wednesday": [
        (to_minutes(9, 0),  to_minutes(11, 30)),
        (to_minutes(12, 0), to_minutes(12, 30)),
        (to_minutes(13, 0), to_minutes(14, 0)),
        (to_minutes(14, 30), to_minutes(16, 0)),
        (to_minutes(16, 30), to_minutes(17, 0)),
    ],
}

def overlaps(a_start, a_end, b_start, b_end):
    return a_start < b_end and a_end > b_start

def jennifer_free(day, start):
    end = start + DURATION
    for b_start, b_end in busy_jennifer.get(day, []):
        if overlaps(start, end, b_start, b_end):
            return False
    return True

# John's constraints:
# - Avoid meetings on Tuesday and Wednesday.
# - Avoid meetings on Monday after 14:30 (i.e., start times must be <= 14:30).
def john_pref(day, start):
    if day == "Monday":
        return start <= to_minutes(14, 30)
    return False  # Tuesday and Wednesday not preferred/allowed

# Create the problem
problem = Problem()
problem.addVariable("day", ["Monday", "Tuesday", "Wednesday"])
problem.addVariable("start", all_starts)

# Add constraints
problem.addConstraint(jennifer_free, ("day", "start"))
problem.addConstraint(john_pref, ("day", "start"))

# Find solutions and pick the earliest by day then time
solutions = problem.getSolutions()

if not solutions:
    # Fallback (should not happen as per problem statement)
    print("No solution found")
else:
    day_order = {"Monday": 0, "Tuesday": 1, "Wednesday": 2}
    solutions.sort(key=lambda s: (day_order[s["day"]], s["start"]))
    best = solutions[0]
    start_str = fmt_time(best["start"])
    end_str = fmt_time(best["start"] + DURATION)
    # Output must include both the day and the time range like {HH:MM:HH:MM}
    print(f"{best['day']} {{{start_str}:{end_str}}}")