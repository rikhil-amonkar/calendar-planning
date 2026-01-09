from constraint import Problem

# Time helpers
def to_minutes(h, m):
    return h * 60 + m

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours and meeting duration
WORK_START = to_minutes(9, 0)   # 09:00
WORK_END = to_minutes(17, 0)    # 17:00
DURATION = 30                   # 30 minutes
STEP = 30                       # Search in 30-minute increments

# Participants' busy schedules (minutes from midnight)
schedules = {
    "Bobby": {
        "Monday": [
            (to_minutes(14, 30), to_minutes(15, 0)),
        ],
        "Tuesday": [
            (to_minutes(9, 0), to_minutes(11, 30)),
            (to_minutes(12, 0), to_minutes(12, 30)),
            (to_minutes(13, 0), to_minutes(15, 0)),
            (to_minutes(15, 30), to_minutes(17, 0)),
        ],
    },
    "Michael": {
        "Monday": [
            (to_minutes(9, 0), to_minutes(10, 0)),
            (to_minutes(10, 30), to_minutes(13, 30)),
            (to_minutes(14, 0), to_minutes(15, 0)),
            (to_minutes(15, 30), to_minutes(17, 0)),
        ],
        "Tuesday": [
            (to_minutes(9, 0), to_minutes(10, 30)),
            (to_minutes(11, 0), to_minutes(11, 30)),
            (to_minutes(12, 0), to_minutes(14, 0)),
            (to_minutes(15, 0), to_minutes(16, 0)),
            (to_minutes(16, 30), to_minutes(17, 0)),
        ],
    },
}

days = ["Monday", "Tuesday"]

# Build the CSP
problem = Problem()
problem.addVariable("Day", days)
start_domain = list(range(WORK_START, WORK_END - DURATION + 1, STEP))
problem.addVariable("Start", start_domain)

# Availability constraint across all participants for the chosen day
def availability_constraint(day, start):
    end = start + DURATION
    # ensure within work hours (redundant due to domain, but kept for safety)
    if not (WORK_START <= start and end <= WORK_END):
        return False
    for person in schedules:
        for b_start, b_end in schedules[person][day]:
            # overlap if start < busy_end and end > busy_start
            if start < b_end and end > b_start:
                return False
    return True

problem.addConstraint(availability_constraint, ("Day", "Start"))

solutions = problem.getSolutions()

if not solutions:
    print("No feasible meeting time found.")
else:
    day_order = {d: i for i, d in enumerate(days)}
    best = min(solutions, key=lambda s: (day_order[s["Day"]], s["Start"]))
    day = best["Day"]
    start = best["Start"]
    end = start + DURATION
    print(f"{day} {{{format_time(start)}:{format_time(end)}}}")