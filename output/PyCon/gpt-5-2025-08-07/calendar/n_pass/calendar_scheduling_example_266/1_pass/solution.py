# Requires: python-constraint
# pip install python-constraint

from constraint import Problem, AllEqualConstraint

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
all_start_times = list(range(work_start, work_end - duration + 1, duration))

# Participants' busy schedules (inclusive of start, exclusive of end)
busy = {
    "Joe": [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("10:30"), to_minutes("11:00")),
    ],
    "Keith": [
        (to_minutes("11:30"), to_minutes("12:00")),
        (to_minutes("15:00"), to_minutes("15:30")),
    ],
    "Patricia": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
    ],
    "Nancy": [
        (to_minutes("09:00"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("16:30")),
    ],
    "Pamela": [
        (to_minutes("09:00"), to_minutes("10:00")),
        (to_minutes("10:30"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("14:00")),
        (to_minutes("14:30"), to_minutes("15:00")),
        (to_minutes("15:30"), to_minutes("16:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ],
}

def is_free(start, blocks):
    end = start + duration
    for b_start, b_end in blocks:
        # overlap if start < b_end and end > b_start
        if start < b_end and end > b_start:
            return False
    return True

# Build domains for each participant
domains = {}
for person, blocks in busy.items():
    domains[person] = [t for t in all_start_times if is_free(t, blocks)]

# Set up CSP
problem = Problem()
for person, domain in domains.items():
    problem.addVariable(person, domain)

# All must meet at the same start time
problem.addConstraint(AllEqualConstraint(), list(busy.keys()))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose the earliest feasible time
earliest_start = min(sol[next(iter(sol))] for sol in solutions)
start_str = to_hhmm(earliest_start)
end_str = to_hhmm(earliest_start + duration)

# Output must include both the time range in braces and the day of the week
print(f"{day} {{{start_str}:{end_str}}}")