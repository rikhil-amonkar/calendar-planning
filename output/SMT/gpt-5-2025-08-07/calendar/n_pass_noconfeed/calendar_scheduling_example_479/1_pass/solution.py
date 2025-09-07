from z3 import *

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Problem setup
day = "Monday"
work_start = to_minutes("09:00")
work_end   = to_minutes("17:00")
duration = 60  # minutes

# Participants' busy intervals on Monday
calendars = {
    "Evelyn": [],
    "Joshua": [("11:00","12:30"), ("13:30","14:30"), ("16:30","17:00")],
    "Kevin": [],
    "Gerald": [],
    "Jerry":  [("09:00","09:30"), ("10:30","12:00"), ("12:30","13:00"),
               ("13:30","14:00"), ("14:30","15:00"), ("15:30","16:00")],
    "Jesse":  [("09:00","09:30"), ("10:30","12:00"), ("12:30","13:00"),
               ("14:30","15:00"), ("15:30","16:30")],
    "Kenneth":[("10:30","12:30"), ("13:30","14:00"), ("14:30","15:00"),
               ("15:30","16:00"), ("16:30","17:00")],
}

# Build constraints
solver = Solver()
start = Int("start")

# Meeting must be within work hours
solver.add(start >= work_start)
solver.add(start + duration <= work_end)

# Align starts on 30-minute boundaries for clean scheduling
solver.add(start % 30 == 0)

# Add non-overlap constraints for all busy intervals
for person, intervals in calendars.items():
    for s, e in intervals:
        bs, be = to_minutes(s), to_minutes(e)
        # Meeting [start, start+duration) must not overlap [bs, be)
        solver.add(Or(start + duration <= bs, start >= be))

# Solve
if solver.check() == sat:
    model = solver.model()
    start_time = model[start].as_long()
    end_time = start_time + duration
    print(f"{day} {{{fmt_time(start_time)}:{fmt_time(end_time)}}}")
else:
    print("No feasible meeting time found.")