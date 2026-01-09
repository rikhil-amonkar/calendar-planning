# Requires: python-constraint (pip install python-constraint)
from constraint import Problem

def to_min(h, m):
    return h * 60 + m

def fmt_time(m):
    return f"{m//60:02d}:{m%60:02d}"

# Meeting parameters
WORK_START = to_min(9, 0)
WORK_END = to_min(17, 0)
MEETING_DURATION = 60  # minutes
DAYS = ["Monday", "Tuesday"]

# Participants' busy schedules (minutes from midnight)
busy = {
    "Patricia": {
        "Monday": [
            (to_min(10, 0), to_min(10, 30)),
            (to_min(11, 30), to_min(12, 0)),
            (to_min(13, 0), to_min(13, 30)),
            (to_min(14, 30), to_min(15, 30)),
            (to_min(16, 0), to_min(16, 30)),
        ],
        "Tuesday": [
            (to_min(10, 0), to_min(10, 30)),
            (to_min(11, 0), to_min(12, 0)),
            (to_min(14, 0), to_min(16, 0)),
            (to_min(16, 30), to_min(17, 0)),
        ],
    },
    "Jesse": {
        "Monday": [
            (to_min(9, 0), to_min(17, 0)),
        ],
        "Tuesday": [
            (to_min(11, 0), to_min(11, 30)),
            (to_min(12, 0), to_min(12, 30)),
            (to_min(13, 0), to_min(14, 0)),
            (to_min(14, 30), to_min(15, 0)),
            (to_min(15, 30), to_min(17, 0)),
        ],
    }
}

# Generate possible start times at 30-minute granularity
start_times = [t for t in range(WORK_START, WORK_END - MEETING_DURATION + 1, 30)]

def no_overlap(start, end, intervals):
    for s, e in intervals:
        if not (end <= s or start >= e):
            return False
    return True

problem = Problem()
problem.addVariable("day", DAYS)
problem.addVariable("start", start_times)

def constraint(day, start):
    end = start + MEETING_DURATION
    if not (WORK_START <= start and end <= WORK_END):
        return False
    # Check all participants for the given day
    for person in busy:
        if not no_overlap(start, end, busy[person][day]):
            return False
    return True

problem.addConstraint(constraint, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    print("No solution found")
else:
    # Prefer earliest day then earliest time
    day_order = {d: i for i, d in enumerate(DAYS)}
    solutions.sort(key=lambda s: (day_order[s["day"]], s["start"]))
    sol = solutions[0]
    day = sol["day"]
    start = sol["start"]
    end = start + MEETING_DURATION
    start_s = fmt_time(start)
    end_s = fmt_time(end)
    # Output day and time range in required formats
    print(day)
    print(f"{{{start_s}:{end_s}}}")