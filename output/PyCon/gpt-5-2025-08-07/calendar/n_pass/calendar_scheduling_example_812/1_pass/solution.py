# Requires: python-constraint
from constraint import Problem

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting parameters
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday"]
WORK_START = to_min("09:00")
WORK_END = to_min("17:00")
DURATION = 30  # minutes

# Participants' busy schedules (inclusive start, exclusive end)
busy = {
    "Mary": {
        "Tuesday":   [(to_min("10:00"), to_min("10:30")),
                      (to_min("15:30"), to_min("16:00"))],
        "Wednesday": [(to_min("09:30"), to_min("10:00")),
                      (to_min("15:00"), to_min("15:30"))],
        "Thursday":  [(to_min("09:00"), to_min("10:00")),
                      (to_min("10:30"), to_min("11:30"))],
    },
    "Alexis": {
        "Monday":    [(to_min("09:00"), to_min("10:00")),
                      (to_min("10:30"), to_min("12:00")),
                      (to_min("12:30"), to_min("16:30"))],
        "Tuesday":   [(to_min("09:00"), to_min("10:00")),
                      (to_min("10:30"), to_min("11:30")),
                      (to_min("12:00"), to_min("15:30")),
                      (to_min("16:00"), to_min("17:00"))],
        "Wednesday": [(to_min("09:00"), to_min("11:00")),
                      (to_min("11:30"), to_min("17:00"))],
        "Thursday":  [(to_min("10:00"), to_min("12:00")),
                      (to_min("14:00"), to_min("14:30")),
                      (to_min("15:30"), to_min("16:00")),
                      (to_min("16:30"), to_min("17:00"))],
    }
}

# Construct CSP
problem = Problem()
problem.addVariable("day", DAYS)
# Start times in 30-min increments within work hours
start_domain = list(range(WORK_START, WORK_END - DURATION + 1, 30))
problem.addVariable("start", start_domain)

def no_conflict(day, start):
    end = start + DURATION
    # Ensure within work hours (redundant given domain, but explicit)
    if start < WORK_START or end > WORK_END:
        return False
    # Check all participants for the chosen day
    for person, sched in busy.items():
        for (s, e) in sched.get(day, []):
            # Overlap if not (end <= s or start >= e)
            if not (end <= s or start >= e):
                return False
    return True

problem.addConstraint(no_conflict, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose earliest by day order then time
day_index = {d: i for i, d in enumerate(DAYS)}
solutions.sort(key=lambda sol: (day_index[sol["day"]], sol["start"]))

chosen = solutions[0]
day = chosen["day"]
start = chosen["start"]
end = start + DURATION

start_str = to_hhmm(start)
end_str = to_hhmm(end)

# Output must include the time range and the day of the week
# Include both a plain HH:MM:HH:MM and the {HH:MM:HH:MM} form
print(day)
print(f"{{{start_str}:{end_str}}}")
print(f"{start_str}:{end_str}")