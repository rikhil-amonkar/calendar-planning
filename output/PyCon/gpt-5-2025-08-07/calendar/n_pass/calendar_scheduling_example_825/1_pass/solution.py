from constraint import Problem

# Meeting parameters
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes
MEETING_DURATION = 60 # 1 hour
INCREMENT = 30        # 30-minute increments

def t(h, m):
    return h * 60 + m

def parse(hhmm):
    h, m = map(int, hhmm.split(":"))
    return t(h, m)

def minutes_to_str(m):
    return f"{m//60:02d}:{m%60:02d}"

# Busy schedules for each participant
schedules = {
    "Laura": {
        "Monday":   [(parse("10:30"), parse("11:00")),
                     (parse("12:30"), parse("13:00")),
                     (parse("14:30"), parse("15:30")),
                     (parse("16:00"), parse("17:00"))],
        "Tuesday":  [(parse("09:30"), parse("10:00")),
                     (parse("11:00"), parse("11:30")),
                     (parse("13:00"), parse("13:30")),
                     (parse("14:30"), parse("15:00")),
                     (parse("16:00"), parse("17:00"))],
        "Wednesday":[(parse("11:30"), parse("12:00")),
                     (parse("12:30"), parse("13:00")),
                     (parse("15:30"), parse("16:30"))],
        "Thursday": [(parse("10:30"), parse("11:00")),
                     (parse("12:00"), parse("13:30")),
                     (parse("15:00"), parse("15:30")),
                     (parse("16:00"), parse("16:30"))],
    },
    "Philip": {
        "Monday":   [(parse("09:00"), parse("17:00"))],
        "Tuesday":  [(parse("09:00"), parse("11:00")),
                     (parse("11:30"), parse("12:00")),
                     (parse("13:00"), parse("13:30")),
                     (parse("14:00"), parse("14:30")),
                     (parse("15:00"), parse("16:30"))],
        "Wednesday":[(parse("09:00"), parse("10:00")),
                     (parse("11:00"), parse("12:00")),
                     (parse("12:30"), parse("16:00")),
                     (parse("16:30"), parse("17:00"))],
        "Thursday": [(parse("09:00"), parse("10:30")),
                     (parse("11:00"), parse("12:30")),
                     (parse("13:00"), parse("17:00"))],
    }
}

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

def is_free(person, day, start, duration):
    end = start + duration
    if start < WORK_START or end > WORK_END:
        return False
    for bs, be in schedules.get(person, {}).get(day, []):
        # Check overlap between [start, end) and [bs, be)
        if not (end <= bs or start >= be):
            return False
    return True

# Build solver
problem = Problem()
problem.addVariable("Day", days)
# Philip cannot meet on Wednesday
problem.addConstraint(lambda d: d != "Wednesday", ["Day"])

possible_starts = list(range(WORK_START, WORK_END - MEETING_DURATION + 1, INCREMENT))
problem.addVariable("Start", possible_starts)

# Both participants must be free for the full duration
def availability_constraint(day, start):
    return is_free("Laura", day, start, MEETING_DURATION) and is_free("Philip", day, start, MEETING_DURATION)

problem.addConstraint(availability_constraint, ["Day", "Start"])

solutions = problem.getSolutions()

if not solutions:
    # As per problem statement, a solution exists; this is just a fallback.
    print("No feasible time found")
else:
    day_order = {d: i for i, d in enumerate(days)}
    best = min(solutions, key=lambda s: (day_order[s["Day"]], s["Start"]))
    start = best["Start"]
    end = start + MEETING_DURATION
    start_str = minutes_to_str(start)
    end_str = minutes_to_str(end)
    # Output required time range and day
    print(f"{{{start_str}:{end_str}}}")
    print(best["Day"])