from constraint import Problem

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

# Parameters
meeting_day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Busy schedules (start, end) in minutes from midnight
busy = {
    "John": [(to_minutes("11:30"), to_minutes("12:00")),
             (to_minutes("14:00"), to_minutes("14:30"))],
    "Megan": [(to_minutes("12:00"), to_minutes("12:30")),
              (to_minutes("14:00"), to_minutes("15:00")),
              (to_minutes("15:30"), to_minutes("16:00"))],
    "Brandon": [],
    "Kimberly": [(to_minutes("09:00"), to_minutes("09:30")),
                 (to_minutes("10:00"), to_minutes("10:30")),
                 (to_minutes("11:00"), to_minutes("14:30")),
                 (to_minutes("15:00"), to_minutes("16:00")),
                 (to_minutes("16:30"), to_minutes("17:00"))],
    "Sean": [(to_minutes("10:00"), to_minutes("11:00")),
             (to_minutes("11:30"), to_minutes("14:00")),
             (to_minutes("15:00"), to_minutes("15:30"))],
    "Lori": [(to_minutes("09:00"), to_minutes("09:30")),
             (to_minutes("10:30"), to_minutes("12:00")),
             (to_minutes("13:00"), to_minutes("14:30")),
             (to_minutes("16:00"), to_minutes("16:30"))],
}

# Create the problem
problem = Problem()

# Consider 30-minute aligned start times within work hours
start_times = list(range(work_start, work_end - duration + 1, 30))
problem.addVariable("start", start_times)

def no_overlap(start):
    end = start + duration
    for intervals in busy.values():
        for s, e in intervals:
            # Overlap if not (meeting ends before busy starts OR meeting starts after busy ends)
            if not (end <= s or start >= e):
                return False
    return True

problem.addConstraint(no_overlap, ["start"])

# Solve and choose the earliest feasible slot
solutions = problem.getSolutions()
if not solutions:
    raise SystemExit("No feasible meeting time found.")

best_start = min(solutions, key=lambda sol: sol["start"])["start"]
best_end = best_start + duration

# Output day and time range in required format
print(meeting_day)
print(f"{{{fmt(best_start)}:{fmt(best_end)}}}")