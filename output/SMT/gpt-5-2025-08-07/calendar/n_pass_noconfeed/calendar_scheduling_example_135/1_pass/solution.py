from z3 import *

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_str(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Participants' busy schedules on Monday
participants_busy = {
    "Eric": [],
    "Ashley": [("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00")],
    "Ronald": [("09:00", "09:30"), ("10:00", "11:30"), ("12:30", "14:00"), ("14:30", "17:00")],
    "Larry": [("09:00", "12:00"), ("13:00", "17:00")],
}

# Convert all busy intervals to minutes
busy_minutes = {}
for person, intervals in participants_busy.items():
    busy_minutes[person] = [(to_minutes(s), to_minutes(e)) for (s, e) in intervals]

# Z3 variables
start = Int("start")
end = Int("end")

s = Solver()

# Duration and work hours constraints
s.add(end == start + duration)
s.add(start >= work_start, end <= work_end)

# No overlap with any participant's busy intervals
for person, intervals in busy_minutes.items():
    for (b_start, b_end) in intervals:
        # Meeting must be entirely before or after each busy interval
        s.add(Or(end <= b_start, start >= b_end))

# Find a solution
if s.check() == sat:
    model = s.model()
    start_min = model[start].as_long()
    end_min = model[end].as_long()
    start_str = minutes_to_str(start_min)
    end_str = minutes_to_str(end_min)
    # Output includes both the day and the time range in {HH:MM:HH:MM} format
    print(day)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No feasible meeting time found.")