from z3 import *

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def minutes_to_hhmm(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Problem setup
day_of_week = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes

# Busy schedules (inclusive of start, exclusive of end)
busy = {
    "Gregory":   [("09:00","09:30"), ("11:30","12:00")],
    "Jonathan":  [("09:00","09:30"), ("12:00","12:30"), ("13:00","13:30"), ("15:00","16:00"), ("16:30","17:00")],
    "Barbara":   [("10:00","10:30"), ("13:30","14:00")],
    "Jesse":     [("10:00","11:00"), ("12:30","14:30")],
    "Alan":      [("09:30","11:00"), ("11:30","12:30"), ("13:00","15:30"), ("16:00","17:00")],
    "Nicole":    [("09:00","10:30"), ("11:30","12:00"), ("12:30","13:30"), ("14:00","17:00")],
    "Catherine": [("09:00","10:30"), ("12:00","13:30"), ("15:00","15:30"), ("16:00","16:30")],
}

# Convert all busy intervals to minutes
busy_minutes = {
    person: [(to_minutes(s), to_minutes(e)) for (s, e) in intervals]
    for person, intervals in busy.items()
}

# Z3 model
s = Int("start")  # meeting start time in minutes from midnight
e = Int("end")    # meeting end time in minutes from midnight

solver = Solver()
solver.add(e == s + meeting_duration)

# Meeting must be within work hours
solver.add(s >= work_start, e <= work_end)

# Optional: start times aligned to 30-minute boundaries
solver.add(s % 30 == 0)

# No overlap with any participant's busy intervals
for person, intervals in busy_minutes.items():
    for (bs, be) in intervals:
        solver.add(Or(e <= bs, s >= be))

if solver.check() == sat:
    model = solver.model()
    start_val = model[s].as_long()
    end_val = model[e].as_long()
    start_str = minutes_to_hhmm(start_val)
    end_str = minutes_to_hhmm(end_val)
    print(f"{{{start_str}:{end_str}}}")
    print(day_of_week)
else:
    print("No valid time found")
    print(day_of_week)