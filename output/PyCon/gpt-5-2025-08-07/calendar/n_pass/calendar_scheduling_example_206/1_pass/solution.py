# Requires: python-constraint
from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

def overlaps(a_start, a_end, b_start, b_end):
    return a_start < b_end and b_start < a_end  # [start, end)

def is_free(start, duration, busy_intervals):
    end = start + duration
    return all(not overlaps(start, end, s, e) for (s, e) in busy_intervals)

def generate_slots(day_start, day_end, step, duration):
    return list(range(day_start, day_end - duration + 1, step))

# Meeting parameters
DAY = "Monday"
MEETING_DURATION = 30  # minutes
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
STEP = 30  # 30-minute granularity

participants = ["Shirley", "Jacob", "Stephen", "Margaret", "Mason"]

busy = {
    "Shirley": [(to_minutes("10:30"), to_minutes("11:00")),
                (to_minutes("12:00"), to_minutes("12:30"))],
    "Jacob":   [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:00"), to_minutes("10:30")),
                (to_minutes("11:00"), to_minutes("11:30")),
                (to_minutes("12:30"), to_minutes("13:30")),
                (to_minutes("14:30"), to_minutes("15:00"))],
    "Stephen": [(to_minutes("11:30"), to_minutes("12:00")),
                (to_minutes("12:30"), to_minutes("13:00"))],
    "Margaret":[(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:30"), to_minutes("12:30")),
                (to_minutes("13:00"), to_minutes("13:30")),
                (to_minutes("15:00"), to_minutes("15:30")),
                (to_minutes("16:30"), to_minutes("17:00"))],
    "Mason":   [(to_minutes("09:00"), to_minutes("10:00")),
                (to_minutes("10:30"), to_minutes("11:00")),
                (to_minutes("11:30"), to_minutes("12:30")),
                (to_minutes("13:00"), to_minutes("13:30")),
                (to_minutes("14:00"), to_minutes("14:30")),
                (to_minutes("16:30"), to_minutes("17:00"))],
}

# Generate base candidate start times within work hours
base_slots = generate_slots(WORK_START, WORK_END, STEP, MEETING_DURATION)

# Domains per participant with constraints applied
domains = {}

for p in participants:
    # Start with all base slots that don't overlap with each participant's busy times
    allowed = [s for s in base_slots if is_free(s, MEETING_DURATION, busy[p])]

    # Additional preference: Margaret does not want to meet before 14:30
    if p == "Margaret":
        cutoff = to_minutes("14:30")
        allowed = [s for s in allowed if s >= cutoff]

    domains[p] = allowed

# Set up constraint problem
problem = Problem()
for p in participants:
    problem.addVariable(p, domains[p])

def all_equal(*vals):
    return len(set(vals)) == 1

problem.addConstraint(all_equal, participants)

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No feasible meeting time found.")

# Choose the earliest valid meeting time
earliest_start = min(sol[participants[0]] for sol in solutions)  # all equal, any participant key works
start_str = to_hhmm(earliest_start)
end_str = to_hhmm(earliest_start + MEETING_DURATION)

# Output in required formats
# 1) Time in HH:MM:HH:MM
print(f"{start_str}:{end_str}")
# 2) Time enclosed in braces
print(f"{{{start_str}:{end_str}}}")
# 3) Day of the week
print(DAY)