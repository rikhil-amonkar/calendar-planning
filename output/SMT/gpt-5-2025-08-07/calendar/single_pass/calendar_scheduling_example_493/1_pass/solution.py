from z3 import Optimize, Int, Or

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Work hours and meeting duration
day = "Monday"
day_start = to_minutes("09:00")
day_end = to_minutes("17:00")
duration = 30  # minutes

# Busy schedules (inclusive of start, exclusive of end)
schedules = {
    "Tyler": [],
    "Kelly": [],
    "Stephanie": [("11:00", "11:30"), ("14:30", "15:00")],
    "Hannah": [],
    "Joe": [("09:00", "09:30"), ("10:00", "12:00"), ("12:30", "13:00"), ("14:00", "17:00")],
    "Diana": [("09:00", "10:30"), ("11:30", "12:00"), ("13:00", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
    "Deborah": [("09:00", "10:00"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "16:30")],
}

# Convert schedules to minutes
busy = {}
for person, intervals in schedules.items():
    busy[person] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

# Z3 model
start = Int("start")
opt = Optimize()

# Within work hours
opt.add(start >= day_start)
opt.add(start + duration <= day_end)

# Half-hour granularity
opt.add((start - day_start) % 30 == 0)

# No overlap with any busy interval for each participant
for person, intervals in busy.items():
    for (b_start, b_end) in intervals:
        # Meeting [start, start+duration) must be entirely before busy interval
        # or entirely after it
        opt.add(Or(start + duration <= b_start, start >= b_end))

# Choose the earliest feasible time (optional but deterministic)
opt.minimize(start)

if opt.check() == 1:  # sat
    m = opt.model()
    s = m[start].as_long()
    e = s + duration
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_minutes(s)}")
    print(f"End Time: {fmt_minutes(e)}")
else:
    # Per problem statement, a solution exists, but handle gracefully just in case
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 00:00")
    print("End Time: 00:00")