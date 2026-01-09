from constraint import Problem

# Helper functions
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def overlaps(start, dur, busy_start, busy_end):
    end = start + dur
    return not (end <= busy_start or start >= busy_end)

# Setup
days = ["Monday", "Tuesday", "Wednesday"]
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30

# Busy schedules (minutes since midnight)
busy = {
    "Susan": {
        "Monday":    [(to_minutes("12:30"), to_minutes("13:00")),
                      (to_minutes("13:30"), to_minutes("14:00"))],
        "Tuesday":   [(to_minutes("11:30"), to_minutes("12:00"))],
        "Wednesday": [(to_minutes("09:30"), to_minutes("10:30")),
                      (to_minutes("14:00"), to_minutes("14:30")),
                      (to_minutes("15:30"), to_minutes("16:30"))],
    },
    "Sandra": {
        "Monday":    [(to_minutes("09:00"), to_minutes("13:00")),
                      (to_minutes("14:00"), to_minutes("15:00")),
                      (to_minutes("16:00"), to_minutes("16:30"))],
        "Tuesday":   [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("10:30"), to_minutes("12:00")),
                      (to_minutes("12:30"), to_minutes("13:30")),
                      (to_minutes("14:00"), to_minutes("14:30")),
                      (to_minutes("16:00"), to_minutes("17:00"))],
        "Wednesday": [(to_minutes("09:00"), to_minutes("11:30")),
                      (to_minutes("12:00"), to_minutes("12:30")),
                      (to_minutes("13:00"), to_minutes("17:00"))],
    }
}

# Build allowable meeting domain considering work hours and hard constraints
domain = []
for day in days:
    for start in range(work_start, work_end - duration + 1, 30):
        # Sandra cannot meet on Monday after 16:00 (no starts at/after 16:00)
        if day == "Monday" and start >= to_minutes("16:00"):
            continue

        # Check conflicts for all participants
        conflict = False
        for person in busy:
            for bstart, bend in busy[person][day]:
                if overlaps(start, duration, bstart, bend):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            domain.append((day, start))

# Solve with python-constraint
problem = Problem()
problem.addVariable("Meeting", domain)
solutions = problem.getSolutions()

# Apply preference: Susan would rather not meet on Tuesday
# Prefer Monday, then Wednesday, then Tuesday. Also pick earliest time.
preference_order = {"Monday": 0, "Wednesday": 1, "Tuesday": 2}

def solution_key(sol):
    day, start = sol["Meeting"]
    return (preference_order[day], start)

if not solutions:
    raise RuntimeError("No feasible meeting time found.")
best = min(solutions, key=solution_key)
day, start = best["Meeting"]
end = start + duration

# Output: include both the day and the time range in {HH:MM:HH:MM}
time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"
print(day)
print("{" + time_range + "}")