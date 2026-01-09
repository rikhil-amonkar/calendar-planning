from constraint import Problem

# Helper functions
def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting parameters
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 60
step = 30  # search in 30-minute increments

# Participants' busy schedules (inclusive of given constraints)
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

betty_busy = {
    "Monday": [(to_minutes("10:00"), to_minutes("10:30")),
               (to_minutes("11:30"), to_minutes("12:30")),
               (to_minutes("16:00"), to_minutes("16:30"))],
    "Tuesday": [(to_minutes("09:30"), to_minutes("10:00")),
                (to_minutes("10:30"), to_minutes("11:00")),
                (to_minutes("12:00"), to_minutes("12:30")),
                (to_minutes("13:30"), to_minutes("15:00")),
                (to_minutes("16:30"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("13:30"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("15:00"))],
    "Thursday": [],
    "Friday": [(to_minutes("09:00"), to_minutes("10:00")),
               (to_minutes("11:30"), to_minutes("12:00")),
               (to_minutes("12:30"), to_minutes("13:00")),
               (to_minutes("14:30"), to_minutes("15:00"))],
}

megan_busy = {
    "Monday": [(to_minutes("09:00"), to_minutes("17:00"))],  # fully blocked
    "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:00"), to_minutes("10:30")),
                (to_minutes("12:00"), to_minutes("14:00")),
                (to_minutes("15:00"), to_minutes("15:30")),
                (to_minutes("16:00"), to_minutes("16:30"))],
    "Wednesday": [(to_minutes("09:30"), to_minutes("10:30")),
                  (to_minutes("11:00"), to_minutes("11:30")),
                  (to_minutes("12:30"), to_minutes("13:00")),
                  (to_minutes("13:30"), to_minutes("14:30")),
                  (to_minutes("15:30"), to_minutes("17:00"))],
    "Thursday": [(to_minutes("09:00"), to_minutes("10:30")),
                 (to_minutes("11:30"), to_minutes("14:00")),
                 (to_minutes("14:30"), to_minutes("15:00")),
                 (to_minutes("15:30"), to_minutes("16:30"))],
    "Friday": [(to_minutes("09:00"), to_minutes("17:00"))],  # fully blocked
}

# Betty cannot meet on Wednesday and Thursday
forbidden_days_for_betty = {"Wednesday", "Thursday"}
allowed_days = [d for d in days if d not in forbidden_days_for_betty]

# Build CSP
problem = Problem()
problem.addVariable("day", allowed_days)
problem.addVariable("start", list(range(work_start, work_end - duration + 1, step)))

def no_overlap(day, start):
    end = start + duration
    # Must be within working hours
    if not (work_start <= start and end <= work_end):
        return False
    # Check against all busy slots for both participants
    for s, e in betty_busy.get(day, []):
        if not (end <= s or start >= e):
            return False
    for s, e in megan_busy.get(day, []):
        if not (end <= s or start >= e):
            return False
    return True

problem.addConstraint(no_overlap, ("day", "start"))

solutions = problem.getSolutions()

# Choose the earliest valid solution by day order then start time
day_order = {d: i for i, d in enumerate(days)}
solutions.sort(key=lambda sol: (day_order[sol["day"]], sol["start"]))

if not solutions:
    raise RuntimeError("No feasible meeting time found.")

sol = solutions[0]
day = sol["day"]
start = sol["start"]
end = start + duration

print(day)
print(f"{{{fmt(start)}:{fmt(end)}}}")