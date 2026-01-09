from constraint import Problem

# Helpers
def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Configuration
MEETING_DURATION = 60  # minutes
WORK_START = to_min("09:00")
WORK_END = to_min("17:00")
TIME_STEP = 30  # minutes (align with schedules)

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
day_index = {d: i for i, d in enumerate(days)}

# Busy schedules (minutes from midnight)
Megan = {
    "Monday":    [(to_min("13:00"), to_min("13:30")), (to_min("14:00"), to_min("15:30"))],
    "Tuesday":   [(to_min("09:00"), to_min("09:30")), (to_min("12:00"), to_min("12:30")), (to_min("16:00"), to_min("17:00"))],
    "Wednesday": [(to_min("09:30"), to_min("10:00")), (to_min("10:30"), to_min("11:30")), (to_min("12:30"), to_min("14:00")), (to_min("16:00"), to_min("16:30"))],
    "Thursday":  [(to_min("13:30"), to_min("14:30")), (to_min("15:00"), to_min("15:30"))],
}

Daniel = {
    "Monday":    [(to_min("10:00"), to_min("11:30")), (to_min("12:30"), to_min("15:00"))],
    "Tuesday":   [(to_min("09:00"), to_min("10:00")), (to_min("10:30"), to_min("17:00"))],
    "Wednesday": [(to_min("09:00"), to_min("10:00")), (to_min("10:30"), to_min("11:30")), (to_min("12:00"), to_min("17:00"))],
    "Thursday":  [(to_min("09:00"), to_min("12:00")), (to_min("12:30"), to_min("14:30")), (to_min("15:00"), to_min("15:30")), (to_min("16:00"), to_min("17:00"))],
}

participants = [Megan, Daniel]

def is_free(person_schedule, day, start, duration):
    end = start + duration
    # Within work hours
    if start < WORK_START or end > WORK_END:
        return False
    # No overlap with busy intervals
    for bs, be in person_schedule.get(day, []):
        if start < be and end > bs:
            return False
    return True

def all_free(day, start):
    return all(is_free(p, day, start, MEETING_DURATION) for p in participants)

# Build CSP
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", list(range(WORK_START, WORK_END - MEETING_DURATION + 1, TIME_STEP)))

problem.addConstraint(lambda d, s: all_free(d, s), ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    # According to the prompt, a solution exists; this is a fallback.
    print("No feasible meeting time found")
else:
    # Earliest by day then start time
    best = sorted(solutions, key=lambda sol: (day_index[sol["day"]], sol["start"]))[0]
    day = best["day"]
    start = best["start"]
    end = start + MEETING_DURATION

    # Output: include both the day and the time range like {HH:MM:HH:MM}
    print(day)
    print(f"{{{fmt(start)}:{fmt(end)}}}")