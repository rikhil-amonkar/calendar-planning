from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
duration = 30  # minutes
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")

# Busy schedules
busy = {
    "Jean": {
        "Monday": [],
        "Tuesday": [(to_minutes("11:30"), to_minutes("12:00")),
                    (to_minutes("16:00"), to_minutes("16:30"))],
    },
    "Doris": {
        "Monday": [(to_minutes("09:00"), to_minutes("11:30")),
                   (to_minutes("12:00"), to_minutes("12:30")),
                   (to_minutes("13:30"), to_minutes("16:00")),
                   (to_minutes("16:30"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("09:00"), to_minutes("17:00"))],
    }
}

# Build the problem
problem = Problem()
problem.addVariable("day", ["Monday", "Tuesday"])
start_domain = list(range(work_start, work_end - duration + 1, 30))
problem.addVariable("start", start_domain)

def no_overlap(day, start):
    end = start + duration
    # Ensure within work hours
    if not (work_start <= start and end <= work_end):
        return False
    # Check against all participants' busy times
    for person in busy:
        for bs, be in busy[person][day]:
            if start < be and end > bs:
                return False
    return True

problem.addConstraint(no_overlap, ("day", "start"))

solutions = problem.getSolutions()

def preference_key(sol):
    # Doris would rather not meet on Monday after 14:00
    start = sol["start"]
    end = start + duration
    day = sol["day"]
    if day == "Monday" and end <= to_minutes("14:00"):
        priority = 0
    elif day == "Monday":
        priority = 1
    else:
        priority = 2
    return (priority, start)

if not solutions:
    raise SystemExit("No valid meeting time found.")

best = sorted(solutions, key=preference_key)[0]
day = best["day"]
start = best["start"]
end = start + duration

print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")