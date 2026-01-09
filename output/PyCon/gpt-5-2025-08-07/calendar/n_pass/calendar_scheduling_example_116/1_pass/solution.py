# Requires: python-constraint
from constraint import Problem, AllEqualConstraint

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    # Intervals [a_start, a_end) and [b_start, b_end) overlap if both conditions hold:
    return a_start < b_end and a_end > b_start

# Meeting details
day = "Monday"
meeting_duration = 30  # minutes
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")

# Generate 30-min aligned candidate starts within work hours
candidate_starts = list(range(work_start, work_end - meeting_duration + 1, 30))

# Participants' busy schedules on Monday (start, end) in minutes
busy = {
    "Adam": [
        (to_minutes("14:00"), to_minutes("15:00")),
    ],
    "John": [
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:00"), to_minutes("14:30")),
        (to_minutes("15:30"), to_minutes("16:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ],
    "Stephanie": [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("10:30"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("16:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ],
    "Anna": [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("15:30")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ],
}

# Anna's preference: not before 14:30 on Monday
anna_not_before = to_minutes("14:30")

def available_domain(person):
    dom = []
    for s in candidate_starts:
        # Apply Anna's time preference
        if person == "Anna" and s < anna_not_before:
            continue
        e = s + meeting_duration
        # Check no overlap with busy intervals
        if all(not overlaps(s, e, b_s, b_e) for (b_s, b_e) in busy[person]):
            dom.append(s)
    return dom

# Setup problem
problem = Problem()
participants = ["Adam", "John", "Stephanie", "Anna"]

for p in participants:
    problem.addVariable(p, available_domain(p))

# All participants must share the same start time
problem.addConstraint(AllEqualConstraint(), participants)

solutions = problem.getSolutions()

# Choose the earliest valid solution (deterministic)
if solutions:
    # Any participant's value is fine since they're constrained equal
    chosen = min(solutions, key=lambda sol: sol["Adam"])
    start = chosen["Adam"]
    end = start + meeting_duration
    print(f"{{{fmt_minutes(start)}:{fmt_minutes(end)}}}")
    print(day)
else:
    # As per prompt, a solution exists; this path should not occur.
    print("No solution found")
    print(day)