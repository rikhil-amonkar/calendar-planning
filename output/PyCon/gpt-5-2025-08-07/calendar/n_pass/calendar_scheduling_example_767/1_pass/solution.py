from constraint import Problem

# Meeting parameters
MEETING_DURATION_MIN = 60
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes

days = ["Monday", "Tuesday", "Wednesday"]

# Blocked schedules (in minutes from 00:00)
blocked = {
    "Monday": {
        "Martha": [(16*60, 17*60)],
        "Beverly": [(9*60, 13*60 + 30), (14*60, 17*60)],
    },
    "Tuesday": {
        "Martha": [(15*60, 15*60 + 30)],
        "Beverly": [(9*60, 17*60)],
    },
    "Wednesday": {
        "Martha": [(10*60, 11*60), (14*60, 14*60 + 30)],
        "Beverly": [(9*60 + 30, 15*60 + 30), (16*60 + 30, 17*60)],
    },
}

def overlaps(a_start, a_end, b_start, b_end):
    return max(a_start, b_start) < min(a_end, b_end)

def is_free(person, day, start, end):
    for s, e in blocked.get(day, {}).get(person, []):
        if overlaps(start, end, s, e):
            return False
    return True

def minutes_to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Build the problem
problem = Problem()
problem.addVariable("day", days)
# Start times at 30-minute granularity, ensuring the meeting ends by WORK_END
start_times = list(range(WORK_START, WORK_END - MEETING_DURATION_MIN + 1, 30))
problem.addVariable("start", start_times)

def availability_constraint(day, start):
    end = start + MEETING_DURATION_MIN
    if not (WORK_START <= start and end <= WORK_END):
        return False
    return is_free("Martha", day, start, end) and is_free("Beverly", day, start, end)

problem.addConstraint(availability_constraint, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    print("No feasible meeting time found.")
else:
    # Choose the earliest by day then start time
    day_order = {d: i for i, d in enumerate(days)}
    solutions.sort(key=lambda s: (day_order[s["day"]], s["start"]))
    best = solutions[0]
    start = best["start"]
    end = start + MEETING_DURATION_MIN
    start_str = minutes_to_hhmm(start)
    end_str = minutes_to_hhmm(end)

    # Output both the day and the time range in required formats
    print(best["day"])
    print(f"{start_str}:{end_str}")
    print(f"{{{start_str}:{end_str}}}")