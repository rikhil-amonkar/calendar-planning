from constraint import Problem

# Helper functions
def minutes(h, m):
    return h * 60 + m

def overlaps(start, end, bstart, bend):
    return start < bend and end > bstart

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
DURATION = 30  # minutes
WORK_START = minutes(9, 0)
WORK_END = minutes(17, 0)
START_TIMES = list(range(WORK_START, WORK_END - DURATION + 1, 30))
DAYS = [0, 1, 2, 3]  # Monday=0, Tuesday=1, Wednesday=2, Thursday=3
DAY_NAMES = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}

# Participants' schedules (busy intervals per day in minutes from midnight)
# Julie: no meetings (no busy intervals)
# Ruth: as specified
busy_intervals = {
    0: [(minutes(9, 0), minutes(17, 0))],  # Monday
    1: [(minutes(9, 0), minutes(17, 0))],  # Tuesday
    2: [(minutes(9, 0), minutes(17, 0))],  # Wednesday
    3: [
        (minutes(9, 0), minutes(11, 0)),
        (minutes(11, 30), minutes(14, 30)),
        (minutes(15, 0), minutes(17, 0)),
    ],  # Thursday
}

# Build CSP
problem = Problem()
problem.addVariable("day", DAYS)
problem.addVariable("start", START_TIMES)

# Availability constraint for Ruth (Julie is free all week)
def ruth_available(day, start):
    end = start + DURATION
    for bstart, bend in busy_intervals.get(day, []):
        if overlaps(start, end, bstart, bend):
            return False
    return True

problem.addConstraint(ruth_available, ["day", "start"])

solutions = problem.getSolutions()

# Preference: Julie would like to avoid Thursday before 11:30
def meets_julie_preference(sol):
    return not (sol["day"] == 3 and sol["start"] < minutes(11, 30))

if not solutions:
    print("No feasible meeting time found.")
else:
    # Prioritize solutions that meet Julie's preference, then by earliest day/time
    solutions.sort(
        key=lambda s: (
            0 if meets_julie_preference(s) else 1,
            s["day"],
            s["start"],
        )
    )
    chosen = solutions[0]
    day_name = DAY_NAMES[chosen["day"]]
    start = chosen["start"]
    end = start + DURATION
    time_range = f"{{{fmt_time(start)}:{fmt_time(end)}}}"
    print(f"{day_name} {time_range}")