# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def blocked_starts(intervals):
    # Convert list of (start_str, end_str) to a set of blocked 30-min start times
    blocked = set()
    for s, e in intervals:
        start = to_minutes(s)
        end = to_minutes(e)
        t = start
        while t + 30 <= end:
            blocked.add(t)
            t += 30
    return blocked

# Work window and possible days
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
start_times = list(range(WORK_START, WORK_END, 30))  # start times from 09:00 to 16:30
days = ["Monday", "Tuesday", "Wednesday"]

# Schedules (busy intervals)
robert_busy = {
    "Monday":    [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
    "Tuesday":   [("10:30", "11:00"), ("15:00", "15:30")],
    "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                  ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
}
ralph_busy = {
    "Monday":    [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
    "Tuesday":   [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "11:30"),
                  ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
    "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"),
                  ("16:30", "17:00")],
}

# Precompute blocked starts for each person/day
robert_blocked = {d: blocked_starts(robert_busy[d]) for d in days}
ralph_blocked  = {d: blocked_starts(ralph_busy[d])  for d in days}

# Set up CSP
problem = Problem()
problem.addVariable("day", days)
problem.addVariable("start", start_times)

def availability(day, start):
    # Meeting is 30 minutes; start within domain ensures end <= 17:00
    return (start not in robert_blocked[day]) and (start not in ralph_blocked[day])

problem.addConstraint(availability, ("day", "start"))

solutions = problem.getSolutions()

# Preference: avoid Monday if possible, then earliest time overall
day_preference = {"Tuesday": 0, "Wednesday": 1, "Monday": 2}
best = min(solutions, key=lambda s: (day_preference[s["day"]], s["start"]))

day = best["day"]
start = best["start"]
end = start + 30

# Output: day on one line, and time range in {HH:MM:HH:MM} on next line
print(day)
print(f"{{{format_time(start)}:{format_time(end)}}}")