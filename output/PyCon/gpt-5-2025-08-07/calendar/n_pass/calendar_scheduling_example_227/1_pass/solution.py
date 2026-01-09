# Requires: python-constraint
# pip install python-constraint

from constraint import Problem

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def make_busy(intervals):
    return [(to_minutes(s), to_minutes(e)) for s, e in intervals]

def no_overlap(start, duration, busy):
    end = start + duration
    for s, e in busy:
        if start < e and end > s:
            return False
    return True

# Problem setup
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' busy schedules (Monday)
natalie_busy = make_busy([])  # wide open
david_busy = make_busy([("11:30", "12:00"), ("14:30", "15:00")])
douglas_busy = make_busy([("09:30", "10:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:00")])
ralph_busy = make_busy([("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:30"),
                        ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")])
jordan_busy = make_busy([("09:00", "10:00"), ("12:00", "12:30"), ("13:00", "13:30"),
                         ("14:30", "15:00"), ("15:30", "17:00")])

# Preference: David does not want to meet before 14:00
david_earliest = to_minutes("14:00")

# Domain: all valid half-hour start times within work hours
domain = list(range(work_start, work_end - duration + 1, 30))

problem = Problem()
problem.addVariable("start", domain)

# Add constraints for each participant
problem.addConstraint(lambda s: no_overlap(s, duration, natalie_busy), ["start"])
problem.addConstraint(lambda s: no_overlap(s, duration, david_busy), ["start"])
problem.addConstraint(lambda s: no_overlap(s, duration, douglas_busy), ["start"])
problem.addConstraint(lambda s: no_overlap(s, duration, ralph_busy), ["start"])
problem.addConstraint(lambda s: no_overlap(s, duration, jordan_busy), ["start"])

# David's time preference
problem.addConstraint(lambda s: s >= david_earliest, ["start"])

solutions = problem.getSolutions()

if not solutions:
    raise SystemExit("No feasible time found.")

# Choose the earliest valid time
best = min(solutions, key=lambda sol: sol["start"])
start = best["start"]
end = start + duration

# Output both the time range and the day of the week
print(f"{day} {{{fmt(start)}:{fmt(end)}}}")