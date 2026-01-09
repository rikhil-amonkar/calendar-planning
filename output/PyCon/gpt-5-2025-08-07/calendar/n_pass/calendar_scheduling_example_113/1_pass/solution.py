from constraint import Problem

# Meeting details
DAY = "Monday"
WORK_START = "09:00"
WORK_END = "17:00"
MEETING_MINUTES = 30

# Participants' blocked intervals on Monday
blocked = {
    "Bradley": [("09:30", "10:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00")],
    "Teresa": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00")],
    "Elizabeth": [("09:00", "09:30"), ("10:30", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Christian": [("09:00", "09:30"), ("10:30", "17:00")],
}

def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def overlaps(a_start, a_end, b_start, b_end) -> bool:
    # Overlap for [start, end) intervals
    return a_start < b_end and b_start < a_end

def slot_available(start_min: int, duration: int, blocks) -> bool:
    end_min = start_min + duration
    for b_start_str, b_end_str in blocks:
        b_start, b_end = to_minutes(b_start_str), to_minutes(b_end_str)
        if overlaps(start_min, end_min, b_start, b_end):
            return False
    return True

# Build domains (start times at 30-min increments)
work_start_min = to_minutes(WORK_START)
work_end_min = to_minutes(WORK_END)
# Last possible start is work_end - meeting_duration
last_start = work_end_min - MEETING_MINUTES

def build_domain(person):
    domain = []
    t = work_start_min
    while t <= last_start:
        if slot_available(t, MEETING_MINUTES, blocked[person]):
            domain.append(t)
        t += 30
    return domain

# Setup CSP
problem = Problem()
participants = list(blocked.keys())
for p in participants:
    problem.addVariable(p, build_domain(p))

# All participants must have the same start time
def all_equal(*vals):
    return len(set(vals)) == 1

problem.addConstraint(all_equal, participants)

solutions = problem.getSolutions()

if not solutions:
    # Guaranteed by the task to exist, but safeguard anyway
    print("No solution found")
else:
    # Choose earliest start time among solutions
    earliest_solution = min(solutions, key=lambda s: s[participants[0]])
    start_min = earliest_solution[participants[0]]
    end_min = start_min + MEETING_MINUTES
    start_str = to_hhmm(start_min)
    end_str = to_hhmm(end_min)
    # Output must include the time range in braces and the day of the week
    print(f"{{{start_str}:{end_str}}}")
    print(DAY)