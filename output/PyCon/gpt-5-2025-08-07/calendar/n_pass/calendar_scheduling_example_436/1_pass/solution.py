from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Work hours and meeting duration
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' busy schedules (Monday)
busy = {
    "Patrick": [(to_minutes("13:30"), to_minutes("14:00")),
                (to_minutes("14:30"), to_minutes("15:00"))],
    "Shirley": [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("11:00"), to_minutes("11:30")),
                (to_minutes("12:00"), to_minutes("12:30")),
                (to_minutes("14:30"), to_minutes("15:00")),
                (to_minutes("16:00"), to_minutes("17:00"))],
    "Jeffrey": [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:30"), to_minutes("11:00")),
                (to_minutes("11:30"), to_minutes("12:00")),
                (to_minutes("13:00"), to_minutes("13:30")),
                (to_minutes("16:00"), to_minutes("17:00"))],
    "Gloria":  [(to_minutes("11:30"), to_minutes("12:00")),
                (to_minutes("15:00"), to_minutes("15:30"))],
    "Nathan":  [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:30"), to_minutes("12:00")),
                (to_minutes("14:00"), to_minutes("17:00"))],
    "Angela":  [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:00"), to_minutes("11:00")),
                (to_minutes("12:30"), to_minutes("15:00")),
                (to_minutes("15:30"), to_minutes("16:30"))],
    "David":   [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:00"), to_minutes("10:30")),
                (to_minutes("11:00"), to_minutes("14:00")),
                (to_minutes("14:30"), to_minutes("16:30"))],
}

# Build problem
problem = Problem()

# Possible start times every 30 minutes within work hours
domain = list(range(work_start, work_end - duration + 1, 30))
problem.addVariable("start", domain)

def no_conflicts_for_all(start):
    meeting_start = start
    meeting_end = start + duration
    # Check against each participant's busy intervals
    for intervals in busy.values():
        for bs, be in intervals:
            # Overlap if [start, end) intersects [bs, be)
            if meeting_start < be and meeting_end > bs:
                return False
    return True

problem.addConstraint(no_conflicts_for_all, ["start"])

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No feasible meeting time found.")

# Choose the earliest feasible start
best = min(solutions, key=lambda s: s["start"])
start = best["start"]
end = start + duration

# Output
print(day)
print(f"{{{fmt(start)}:{fmt(end)}}}")