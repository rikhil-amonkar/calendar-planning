# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Parameters
day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 30  # minutes

# Schedules (busy intervals) in minutes [start, end)
schedules = {
    "Kimberly": [("10:00","10:30"), ("11:00","12:00"), ("16:00","16:30")],
    "Megan":    [],  # preference handled separately
    "Marie":    [("10:00","11:00"), ("11:30","15:00"), ("16:00","16:30")],
    "Diana":    [("09:30","10:00"), ("10:30","14:30"), ("15:30","17:00")],
}

# Convert to minute tuples
busy = {
    person: [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
    for person, intervals in schedules.items()
}

# Preference: Megan would like to avoid meetings before 10:00 on Monday
preference_start = time_to_minutes("10:00")
domain_start = max(work_start, preference_start)
domain = list(range(domain_start, work_end - duration + 1, 30))  # 30-min increments

# Constraint problem
problem = Problem()
problem.addVariable("start", domain)

def availability_constraint(intervals):
    def _c(start):
        s, e = start, start + duration
        for bs, be in intervals:
            # Overlap if s < be and e > bs
            if s < be and e > bs:
                return False
        return True
    return _c

# Add constraints for each participant
for person, intervals in busy.items():
    problem.addConstraint(availability_constraint(intervals), ("start",))

# Ensure meeting within work hours (redundant due to domain, but kept for clarity)
problem.addConstraint(lambda s: work_start <= s and s + duration <= work_end, ("start",))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose the earliest feasible start time
best_start = min(sol["start"] for sol in solutions)
best_end = best_start + duration

time_range = f"{{{minutes_to_time(best_start)}:{minutes_to_time(best_end)}}}"

# Output: include both the time range (with braces) and the day of the week
print(time_range)
print(day)