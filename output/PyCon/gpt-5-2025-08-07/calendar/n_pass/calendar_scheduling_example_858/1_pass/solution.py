# Requires: python-constraint
from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def build_busy(schedule):
    busy = {}
    for day, intervals in schedule.items():
        busy[day] = [(to_minutes(s), to_minutes(e)) for (s, e) in intervals]
    return busy

def is_free(busy_intervals, start_min, duration=60):
    end_min = start_min + duration
    for bs, be in busy_intervals:
        if not (end_min <= bs or start_min >= be):
            return False
    return True

# Participants' busy schedules
carl_schedule = {
    "Monday":    [("11:00", "11:30")],
    "Tuesday":   [("14:30", "15:00")],
    "Wednesday": [("10:00", "11:30"), ("13:00", "13:30")],
    "Thursday":  [("13:30", "14:00"), ("16:00", "16:30")],
}

margaret_schedule = {
    "Monday":    [("9:00", "10:30"), ("11:00", "17:00")],
    "Tuesday":   [("9:30", "12:00"), ("13:30", "14:00"), ("15:30", "17:00")],
    "Wednesday": [("9:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:30"), ("15:00", "17:00")],
    "Thursday":  [("10:00", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")],
}

# Convert to minute-based busy intervals
carl_busy = build_busy(carl_schedule)
margaret_busy = build_busy(margaret_schedule)

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_start = to_minutes("9:00")
work_end = to_minutes("17:00")
duration = 60

# Allowed start times at 30-minute increments within work hours
start_domain = list(range(work_start, work_end - duration + 1, 30))  # 9:00 to 16:00 inclusive

# Precompute allowed starts per day for both participants
allowed_both = {}
for day in days:
    carl_allowed = {s for s in start_domain if is_free(carl_busy.get(day, []), s, duration)}
    marg_allowed = {s for s in start_domain if is_free(margaret_busy.get(day, []), s, duration)}
    allowed_both[day] = carl_allowed & marg_allowed

# Set up CSP
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_domain)

def availability_constraint(day, start):
    return start in allowed_both.get(day, set())

problem.addConstraint(availability_constraint, ("day", "start"))

solutions = problem.getSolutions()

if not solutions:
    # As per problem statement, a solution exists; this is a fallback.
    print("No solution")
else:
    # Preference: avoid Thursday if possible, then earliest day/time
    day_order = {d: i for i, d in enumerate(days)}
    def pref_key(sol):
        day = sol["day"]
        start = sol["start"]
        avoid_thu = 1 if day == "Thursday" else 0
        return (avoid_thu, day_order[day], start)

    best = sorted(solutions, key=pref_key)[0]
    start_min = best["start"]
    end_min = start_min + duration
    start_str = to_hhmm(start_min)
    end_str = to_hhmm(end_min)
    print(best["day"])
    print(f"{{{start_str}:{end_str}}}")