from constraint import Problem

# Utility functions
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def minutes_to_str(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def no_overlap(start, day, busy_intervals, duration=30):
    for (s, e) in busy_intervals.get(day, []):
        # Overlap if intervals intersect with positive length
        if start < e and (start + duration) > s:
            return False
    return True

# Schedules (in minutes)
busy = {
    "Ryan": {
        "Monday": [(to_minutes("09:30"), to_minutes("10:00")),
                   (to_minutes("11:00"), to_minutes("12:00")),
                   (to_minutes("13:00"), to_minutes("13:30")),
                   (to_minutes("15:30"), to_minutes("16:00"))],
        "Tuesday": [(to_minutes("11:30"), to_minutes("12:30")),
                    (to_minutes("15:30"), to_minutes("16:00"))],
        "Wednesday": [(to_minutes("12:00"), to_minutes("13:00")),
                      (to_minutes("15:30"), to_minutes("16:00")),
                      (to_minutes("16:30"), to_minutes("17:00"))],
    },
    "Adam": {
        "Monday": [(to_minutes("09:00"), to_minutes("10:30")),
                   (to_minutes("11:00"), to_minutes("13:30")),
                   (to_minutes("14:00"), to_minutes("16:00")),
                   (to_minutes("16:30"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("09:00"), to_minutes("10:00")),
                    (to_minutes("10:30"), to_minutes("15:30")),
                    (to_minutes("16:00"), to_minutes("17:00"))],
        "Wednesday": [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("10:00"), to_minutes("11:00")),
                      (to_minutes("11:30"), to_minutes("14:30")),
                      (to_minutes("15:00"), to_minutes("15:30")),
                      (to_minutes("16:00"), to_minutes("16:30"))],
    }
}

# Parameters
meeting_duration = 30  # minutes
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")  # exclusive end for meeting end time
# Start times allowed so that start + duration <= work_end
start_times = list(range(work_start, work_end - meeting_duration + 1, 30))

# Constraints:
# - Work hours 09:00-17:00
# - Days: Monday, Tuesday, Wednesday
# - Ryan cannot meet on Wednesday -> restrict days to Monday, Tuesday
allowed_days = ["Monday", "Tuesday"]

# Build CSP
problem = Problem()
problem.addVariable("Day", allowed_days)
problem.addVariable("Start", start_times)

# No-overlap constraints for each participant on chosen Day
problem.addConstraint(
    lambda start, day: no_overlap(start, day, busy["Ryan"], meeting_duration),
    ["Start", "Day"]
)
problem.addConstraint(
    lambda start, day: no_overlap(start, day, busy["Adam"], meeting_duration),
    ["Start", "Day"]
)

solutions = problem.getSolutions()

# Apply preference: Adam would like to avoid Monday before 14:30
pref_cutoff = to_minutes("14:30")
preferred = [s for s in solutions if not (s["Day"] == "Monday" and s["Start"] < pref_cutoff)]

# If no preferred solutions, fall back to any feasible solution
candidates = preferred if preferred else solutions

# Tie-breakers:
# 1) Prefer Tuesday over Monday (aligns with Adam's preference to avoid Monday before 14:30)
# 2) Earliest start time
def day_rank(day):
    if day == "Tuesday":
        return 0
    if day == "Monday":
        return 1
    return 2

best = sorted(candidates, key=lambda s: (day_rank(s["Day"]), s["Start"]))[0]

start = best["Start"]
end = start + meeting_duration
day = best["Day"]

time_range = f"{minutes_to_str(start)}:{minutes_to_str(end)}"

# Output must include both the time range and the day of week
print(f"{{{time_range}}}")
print(day)