from z3 import *

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Meeting parameters
DAY = "Monday"
MEETING_DURATION = 30
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")

# Busy schedules (inclusive of start, exclusive of end)
busy = {
    "Andrea": [("09:30","10:30"), ("13:30","14:30")],
    "Ruth": [("12:30","13:00"), ("15:00","15:30")],
    "Steven": [("10:00","10:30"), ("11:00","11:30"), ("12:00","12:30"), ("13:30","14:00"), ("15:00","16:00")],
    "Grace": [],
    "Kyle": [("09:00","09:30"), ("10:30","12:00"), ("12:30","13:00"), ("13:30","15:00"), ("15:30","16:00"), ("16:30","17:00")],
    "Elijah": [("09:00","11:00"), ("11:30","13:00"), ("13:30","14:00"), ("15:30","16:00"), ("16:30","17:00")],
    "Lori": [("09:00","09:30"), ("10:00","11:30"), ("12:00","13:30"), ("14:00","16:00"), ("16:30","17:00")],
}

# Convert all busy intervals to minutes
busy_minutes = {
    person: [(to_minutes(s), to_minutes(e)) for (s, e) in intervals]
    for person, intervals in busy.items()
}

# Z3 model
opt = Optimize()
start = Int("start")

# Core constraints
opt.add(start >= WORK_START)
opt.add(start + MEETING_DURATION <= WORK_END)
# Optional: align meeting start to 30-minute grid
opt.add(start % 30 == 0)

# No-overlap constraints per participant
for person, intervals in busy_minutes.items():
    for (s, e) in intervals:
        # Enforce: [start, start+dur) does not intersect [s, e)
        opt.add(Or(start + MEETING_DURATION <= s, start >= e))

# Prefer earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    s = m[start].as_long()
    e = s + MEETING_DURATION
    print(f"{DAY} {{{to_hhmm(s)}:{to_hhmm(e)}}}")
else:
    print("No feasible time found.")