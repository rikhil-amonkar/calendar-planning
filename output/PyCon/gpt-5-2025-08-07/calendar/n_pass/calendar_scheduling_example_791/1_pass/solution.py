# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def time_to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

# Meeting parameters
duration = 30  # minutes
work_start = time_to_min("09:00")
work_end = time_to_min("17:00")

# Valid start times (30-minute granularity) within work hours
start_times = list(range(work_start, work_end - duration + 1, 30))

days = ["Monday", "Tuesday", "Wednesday"]

# Busy schedules in minutes since midnight
busy = {
    "Nicole": {
        "Monday":    [(time_to_min("09:00"), time_to_min("09:30")),
                      (time_to_min("13:00"), time_to_min("13:30")),
                      (time_to_min("14:30"), time_to_min("15:30"))],
        "Tuesday":   [(time_to_min("09:00"), time_to_min("09:30")),
                      (time_to_min("11:30"), time_to_min("13:30")),
                      (time_to_min("14:30"), time_to_min("15:30"))],
        "Wednesday": [(time_to_min("10:00"), time_to_min("11:00")),
                      (time_to_min("12:30"), time_to_min("15:00")),
                      (time_to_min("16:00"), time_to_min("17:00"))],
    },
    "Ruth": {
        "Monday":    [(time_to_min("09:00"), time_to_min("17:00"))],
        "Tuesday":   [(time_to_min("09:00"), time_to_min("17:00"))],
        "Wednesday": [(time_to_min("09:00"), time_to_min("10:30")),
                      (time_to_min("11:00"), time_to_min("11:30")),
                      (time_to_min("12:00"), time_to_min("12:30")),
                      (time_to_min("13:30"), time_to_min("15:30")),
                      (time_to_min("16:00"), time_to_min("16:30"))],
    },
}

# Helper to check free status
def is_free(participant, day, start):
    end = start + duration
    for bs, be in busy[participant][day]:
        # Overlap if not (end <= bs or start >= be)
        if not (end <= bs or start >= be):
            return False
    return True

# Ruth preference: not on Wednesday after 13:30
latest_allowed_wed_start = time_to_min("13:30")

problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)

def constraints(day, start):
    # Within work hours already ensured by domain; enforce availability
    if not is_free("Nicole", day, start):
        return False
    if not is_free("Ruth", day, start):
        return False
    # Ruth preference for Wednesday
    if day == "Wednesday" and start > latest_allowed_wed_start:
        return False
    return True

problem.addConstraint(constraints, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible meeting time found.")

# Choose the earliest by day order then time
day_order = {d: i for i, d in enumerate(days)}
best = min(solutions, key=lambda s: (day_order[s["day"]], s["start"]))

start_str = min_to_time(best["start"])
end_str = min_to_time(best["start"] + duration)

# Outputs:
# 1) Exact time range "HH:MM:HH:MM"
print(f"{start_str}:{end_str}")
# 2) Day of the week
print(best["day"])
# 3) Combined with braces as requested example format
print(f"{best['day']} {{{start_str}:{end_str}}}")