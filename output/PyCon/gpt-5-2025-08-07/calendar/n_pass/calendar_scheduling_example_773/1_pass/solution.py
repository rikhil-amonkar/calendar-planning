# Requires: python-constraint
from constraint import Problem

# Time helpers
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting parameters
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 60  # 1 hour
days = ["Monday", "Tuesday", "Wednesday"]

# Participants' busy schedules (in minutes)
roy_busy = {
    "Monday":    [(to_minutes("10:00"), to_minutes("11:30")),
                  (to_minutes("12:00"), to_minutes("13:00")),
                  (to_minutes("14:00"), to_minutes("14:30")),
                  (to_minutes("15:00"), to_minutes("17:00"))],
    "Tuesday":   [(to_minutes("10:30"), to_minutes("11:30")),
                  (to_minutes("12:00"), to_minutes("14:30")),
                  (to_minutes("15:00"), to_minutes("15:30")),
                  (to_minutes("16:00"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:30"), to_minutes("11:30")),
                  (to_minutes("12:30"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("15:30")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
}

# Patrick is free all week; no busy blocks needed

# Build domain for start times in 30-minute increments
start_domain = list(range(work_start, work_end - duration + 1, 30))

# Constraint: meeting must fit within working hours and avoid all busy intervals
def is_valid(day, start):
    end = start + duration
    if start < work_start or end > work_end:
        return False
    # Check Roy's busy times
    for bs, be in roy_busy[day]:
        if not (end <= bs or start >= be):  # overlap
            return False
    # Patrick has no conflicts
    return True

# Set up constraint problem
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_domain)
problem.addConstraint(is_valid, ("day", "start"))

solutions = problem.getSolutions()

# Select earliest: by day order then start time
day_order = {d: i for i, d in enumerate(days)}
best = min(solutions, key=lambda s: (day_order[s["day"]], s["start"]))

start = best["start"]
end = start + duration
time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"
print(f"{{{time_range}}} {best['day']}")