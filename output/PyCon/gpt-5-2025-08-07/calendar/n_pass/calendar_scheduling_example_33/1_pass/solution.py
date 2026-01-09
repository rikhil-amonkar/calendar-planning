# Requires: python-constraint
# pip install python-constraint

from constraint import Problem, AllEqualConstraint

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    # Closed-open intervals [start, end)
    return not (a_end <= b_start or a_start >= b_end)

def allowed_starts(work_start, work_end, duration, step, busy_intervals):
    latest_start = work_end - duration
    starts = []
    for s in range(work_start, latest_start + 1, step):
        e = s + duration
        if all(not overlaps(s, e, bi[0], bi[1]) for bi in busy_intervals):
            starts.append(s)
    return starts

# Parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30
step = 30

# Busy schedules (start, end) in minutes
lisa_busy = [
    (to_minutes("09:00"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("11:30")),
    (to_minutes("12:30"), to_minutes("13:00")),
    (to_minutes("16:00"), to_minutes("16:30")),
]
bobby_busy = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("10:00"), to_minutes("10:30")),
    (to_minutes("11:30"), to_minutes("12:00")),
    (to_minutes("15:00"), to_minutes("15:30")),
]
randy_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("11:00")),
    (to_minutes("11:30"), to_minutes("12:30")),
    (to_minutes("13:00"), to_minutes("13:30")),
    (to_minutes("14:30"), to_minutes("15:30")),
    (to_minutes("16:00"), to_minutes("16:30")),
]

# Domains per participant
lisa_domain = allowed_starts(work_start, work_end, duration, step, lisa_busy)
bobby_domain = allowed_starts(work_start, work_end, duration, step, bobby_busy)
randy_domain = allowed_starts(work_start, work_end, duration, step, randy_busy)

# Set up CSP
problem = Problem()
problem.addVariable("Lisa", lisa_domain)
problem.addVariable("Bobby", bobby_domain)
problem.addVariable("Randy", randy_domain)
problem.addConstraint(AllEqualConstraint(), ["Lisa", "Bobby", "Randy"])

solutions = problem.getSolutions()

# Apply preference: Bobby prefers before 15:00 if possible
preference_cutoff = to_minutes("15:00")
preferred = [s for s in solutions if s["Bobby"] < preference_cutoff]
candidate_solutions = preferred if preferred else solutions

# Choose earliest feasible start
best = min(candidate_solutions, key=lambda s: s["Lisa"])
start = best["Lisa"]
end = start + duration

start_str = to_hhmm(start)
end_str = to_hhmm(end)

# Output must include time range like {HH:MM:HH:MM} and the day of the week
print(f"{{{start_str}:{end_str}}}")
print(day)