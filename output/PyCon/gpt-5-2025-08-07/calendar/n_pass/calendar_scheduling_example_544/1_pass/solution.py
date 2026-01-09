# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def minutes(h, m=0):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Parameters
meeting_duration = 30  # minutes
work_start = minutes(9, 0)
work_end = minutes(17, 0)
day_of_week = "Monday"

# Participants' schedules (busy intervals) in minutes since 00:00
# Deborah: free entire day (no busy constraints)
# Albert: busy intervals and time preference
albert_busy = [
    (minutes(9, 0),  minutes(10, 0)),   # 09:00-10:00
    (minutes(10, 30), minutes(12, 0)),  # 10:30-12:00
    (minutes(15, 0), minutes(16, 30)),  # 15:00-16:30
]
# Albert cannot meet after 11:00 (interpreted as no starts after 11:00)
albert_latest_start = minutes(11, 0)

# Build domain for half-hour start times within work hours
start_domain = list(range(work_start, work_end - meeting_duration + 1, 30))

problem = Problem()
problem.addVariable("day", [day_of_week])
problem.addVariable("start", start_domain)

def within_work_hours(start):
    return work_start <= start and (start + meeting_duration) <= work_end

def no_overlap_with_intervals(start, intervals):
    for s, e in intervals:
        # overlap if [start, start+dur) intersects [s, e)
        if not ((start + meeting_duration) <= s or start >= e):
            return False
    return True

# Constraints
problem.addConstraint(lambda day: day == day_of_week, ("day",))
problem.addConstraint(lambda s: within_work_hours(s), ("start",))
problem.addConstraint(lambda s: no_overlap_with_intervals(s, albert_busy), ("start",))
problem.addConstraint(lambda s: s <= albert_latest_start, ("start",))  # cannot meet after 11:00

solutions = problem.getSolutions()

if not solutions:
    raise RuntimeError("No feasible meeting time found given the constraints.")

# Choose the earliest feasible start time
best = min(solutions, key=lambda sol: sol["start"])
start_min = best["start"]
end_min = start_min + meeting_duration
day = best["day"]

start_str = fmt_time(start_min)
end_str = fmt_time(end_min)

# Output must include both the time range in braces and the day of the week
print(f"{{{start_str}:{end_str}}} {day}")