from constraint import Problem
from datetime import timedelta

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def slot_overlaps(slot_start, slot_end, intervals):
    # Check if [slot_start, slot_end) overlaps any [b_start, b_end)
    for b_start, b_end in intervals:
        if not (slot_end <= b_start or slot_start >= b_end):
            return True
    return False

def allowed_starts(work_start, work_end, duration, busy_intervals):
    starts = []
    s = work_start
    while s + duration <= work_end:
        if not slot_overlaps(s, s + duration, busy_intervals):
            starts.append(s)
        s += 30  # 30-minute granularity
    return starts

# Meeting parameters
day_of_week = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30

# Busy schedules (half-open intervals [start, end))
busy = {
    "Ronald": [],
    "Stephen": [
        (to_minutes("10:00"), to_minutes("10:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
    ],
    "Brittany": [
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("13:30"), to_minutes("14:00")),
        (to_minutes("15:30"), to_minutes("16:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ],
    "Dorothy": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:00"), to_minutes("10:30")),
        (to_minutes("11:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("15:00")),
        (to_minutes("15:30"), to_minutes("17:00")),
    ],
    "Rebecca": [
        (to_minutes("09:30"), to_minutes("10:30")),
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("17:00")),
    ],
    "Jordan": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:00"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("12:00")),
        (to_minutes("13:00"), to_minutes("15:00")),
        (to_minutes("15:30"), to_minutes("16:30")),
    ],
}

participants = list(busy.keys())

# Build domains per participant
domains = {
    p: allowed_starts(work_start, work_end, duration, busy[p]) for p in participants
}

# Set up constraint problem
problem = Problem()
for p in participants:
    problem.addVariable(p, domains[p])

# All participants must share the same start time
problem.addConstraint(lambda *vals: len(set(vals)) == 1, participants)

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No common meeting time found, though one was expected.")

# Choose the earliest valid time
def extract_start(sol):
    # Any participant works since all equal
    return next(iter(sol.values()))

earliest_solution = min(solutions, key=extract_start)
start_minutes = extract_start(earliest_solution)
end_minutes = start_minutes + duration

start_str = to_hhmm(start_minutes)
end_str = to_hhmm(end_minutes)

# Output the day and the time range in required format
print(day_of_week)
print(f"{{{start_str}:{end_str}}}")