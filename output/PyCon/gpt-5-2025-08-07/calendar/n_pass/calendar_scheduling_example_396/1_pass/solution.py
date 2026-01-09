# Requires: python-constraint
from constraint import Problem

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def no_overlap(start, duration, busy_intervals):
    s, e = start, start + duration
    for bs, be in busy_intervals:
        # overlap if not (end <= bs or start >= be)
        if not (e <= bs or s >= be):
            return False
    return True

# Meeting parameters
day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 30  # minutes

# Participants' busy schedules (inclusive of start, exclusive of end)
busy = {
    "Andrea": [],
    "Jack": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
             (time_to_minutes("14:00"), time_to_minutes("14:30"))],
    "Madison": [(time_to_minutes("09:30"), time_to_minutes("10:30")),
                (time_to_minutes("13:00"), time_to_minutes("14:00")),
                (time_to_minutes("15:00"), time_to_minutes("15:30")),
                (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    "Rachel": [(time_to_minutes("09:30"), time_to_minutes("10:30")),
               (time_to_minutes("11:00"), time_to_minutes("11:30")),
               (time_to_minutes("12:00"), time_to_minutes("13:30")),
               (time_to_minutes("14:30"), time_to_minutes("15:30")),
               (time_to_minutes("16:00"), time_to_minutes("17:00"))],
    "Douglas": [(time_to_minutes("09:00"), time_to_minutes("11:30")),
                (time_to_minutes("12:00"), time_to_minutes("16:30"))],
    "Ryan": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
             (time_to_minutes("13:00"), time_to_minutes("14:00")),
             (time_to_minutes("14:30"), time_to_minutes("17:00"))],
}

# Domain: start times on 30-minute increments within work hours
domain = [t for t in range(work_start, work_end - duration + 1, 30)]

problem = Problem()
problem.addVariable("start", domain)

# Add constraints: the chosen start must not overlap any participant's busy times
for person, intervals in busy.items():
    problem.addConstraint(lambda start, iv=intervals: no_overlap(start, duration, iv), ["start"])

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible time found.")

# Choose the earliest valid start time
start_time = min(sol["start"] for sol in solutions)
end_time = start_time + duration

# Output in required format
print(f"{{{minutes_to_time(start_time)}:{minutes_to_time(end_time)}}}")
print(day)