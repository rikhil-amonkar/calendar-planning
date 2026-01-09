# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def hhmm_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting parameters
day = "Monday"
work_start = hhmm_to_minutes("09:00")
work_end = hhmm_to_minutes("17:00")
duration = 30  # minutes

# Busy schedules (inclusive of start, exclusive of end)
patrick_busy = [
    (hhmm_to_minutes("09:00"), hhmm_to_minutes("09:30")),
    (hhmm_to_minutes("10:00"), hhmm_to_minutes("10:30")),
    (hhmm_to_minutes("13:30"), hhmm_to_minutes("14:00")),
    (hhmm_to_minutes("16:00"), hhmm_to_minutes("16:30")),
]
kayla_busy = [
    (hhmm_to_minutes("12:30"), hhmm_to_minutes("13:30")),
    (hhmm_to_minutes("15:00"), hhmm_to_minutes("15:30")),
    (hhmm_to_minutes("16:00"), hhmm_to_minutes("16:30")),
]
carl_busy = [
    (hhmm_to_minutes("10:30"), hhmm_to_minutes("11:00")),
    (hhmm_to_minutes("12:00"), hhmm_to_minutes("12:30")),
    (hhmm_to_minutes("13:00"), hhmm_to_minutes("13:30")),
    (hhmm_to_minutes("14:30"), hhmm_to_minutes("17:00")),
]
christian_busy = [
    (hhmm_to_minutes("09:00"), hhmm_to_minutes("12:30")),
    (hhmm_to_minutes("13:00"), hhmm_to_minutes("14:00")),
    (hhmm_to_minutes("14:30"), hhmm_to_minutes("17:00")),
]

all_busy = patrick_busy + kayla_busy + carl_busy + christian_busy

def is_free(start):
    end = start + duration
    # Must be within working hours
    if start < work_start or end > work_end:
        return False
    # No overlap with any busy interval
    for bs, be in all_busy:
        if not (end <= bs or start >= be):
            return False
    return True

# Build domain of possible start times in 30-minute increments within work hours
domain = list(range(work_start, work_end - duration + 1, 30))

problem = Problem()
problem.addVariable("start", domain)
problem.addConstraint(lambda s: is_free(s), ["start"])

solutions = problem.getSolutions()
if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose the earliest feasible start time
best_start = min(sol["start"] for sol in solutions)
best_end = best_start + duration

start_str = minutes_to_hhmm(best_start)
end_str = minutes_to_hhmm(best_end)

# Output: print the day and the time range in {HH:MM:HH:MM}
print(day)
print(f"{{{start_str}:{end_str}}}")