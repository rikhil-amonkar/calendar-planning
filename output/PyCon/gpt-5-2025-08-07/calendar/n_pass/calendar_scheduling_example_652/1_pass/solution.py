from constraint import Problem

# Helper functions
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def minutes_to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Problem setup
problem = Problem()

# Constants
DAYS = ["Monday", "Tuesday"]
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
DURATION = 30  # minutes
LAST_START = WORK_END - DURATION  # latest start to end within work hours

# Domains
problem.addVariable("day", DAYS)
problem.addVariable("start", list(range(WORK_START, LAST_START + 1, 30)))

# Busy schedules
busy = {
    "Jesse": {
        "Monday": [(to_minutes("13:30"), to_minutes("14:00")),
                   (to_minutes("14:30"), to_minutes("15:00"))],
        "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                    (to_minutes("13:00"), to_minutes("13:30")),
                    (to_minutes("14:00"), to_minutes("15:00"))],
    },
    "Lawrence": {
        "Monday": [(to_minutes("09:00"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("09:30"), to_minutes("10:30")),
                    (to_minutes("11:30"), to_minutes("12:30")),
                    (to_minutes("13:00"), to_minutes("13:30")),
                    (to_minutes("14:30"), to_minutes("15:00")),
                    (to_minutes("15:30"), to_minutes("16:30"))],
    },
}

# Constraints
def within_work_hours(day, start):
    end = start + DURATION
    return WORK_START <= start and end <= WORK_END

def no_overlap(person, day, start):
    end = start + DURATION
    for s, e in busy[person].get(day, []):
        if not (end <= s or start >= e):
            return False
    return True

def lawrence_tuesday_limit(day, start):
    # Lawrence cannot meet on Tuesday after 16:30 -> meeting must end by 16:30 on Tuesday
    end = start + DURATION
    if day == "Tuesday":
        return end <= to_minutes("16:30")
    return True

problem.addConstraint(within_work_hours, ("day", "start"))
problem.addConstraint(lambda day, start: no_overlap("Jesse", day, start), ("day", "start"))
problem.addConstraint(lambda day, start: no_overlap("Lawrence", day, start), ("day", "start"))
problem.addConstraint(lawrence_tuesday_limit, ("day", "start"))

solutions = problem.getSolutions()

# Pick the earliest feasible slot (Monday before Tuesday, then by time)
day_order = {"Monday": 0, "Tuesday": 1}
solutions.sort(key=lambda s: (day_order[s["day"]], s["start"]))

if not solutions:
    print("No feasible time found")
else:
    best = solutions[0]
    day = best["day"]
    start = best["start"]
    end = start + DURATION
    print(f"{day} {{{minutes_to_hhmm(start)}:{minutes_to_hhmm(end)}}}")