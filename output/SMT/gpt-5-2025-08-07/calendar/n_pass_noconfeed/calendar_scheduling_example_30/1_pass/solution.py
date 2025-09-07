from z3 import *

# Helper to convert "HH:MM" to minutes since 00:00
def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Helper to format minutes since 00:00 to "HH:MM"
def fmt(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Problem setup
day = "Monday"
work_start = to_minutes("09:00")
work_end   = to_minutes("17:00")
duration   = 30  # minutes

# Busy intervals per participant (as [start, end) in minutes)
Jeffrey_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("11:00")),
]

Virginia_busy = [
    (to_minutes("09:00"), to_minutes("09:30")),
    (to_minutes("10:00"), to_minutes("10:30")),
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("16:30")),
]

Melissa_busy = [
    (to_minutes("09:00"), to_minutes("11:30")),
    (to_minutes("12:00"), to_minutes("12:30")),
    (to_minutes("13:00"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("17:00")),
]

# Melissa would rather not meet after 14:00 (treat as a hard constraint here)
preference_latest_end = to_minutes("14:00")

# Z3 variables
s = Int("start")  # meeting start time in minutes since 00:00
e = Int("end")    # meeting end time

opt = Optimize()

# Basic constraints: within work hours and fixed duration
opt.add(s >= work_start, e == s + duration, e <= work_end)

# Respect participants' busy intervals: meeting does not overlap any busy interval
def no_overlap(intervals):
    return [Or(e <= a, s >= b) for (a, b) in intervals]

opt.add(no_overlap(Jeffrey_busy))
opt.add(no_overlap(Virginia_busy))
opt.add(no_overlap(Melissa_busy))

# Preference: end no later than 14:00 (as a hard constraint for this task)
opt.add(e <= preference_latest_end)

# Optional: choose the earliest feasible start
opt.minimize(s)

if opt.check() == sat:
    model = opt.model()
    start_val = model[s].as_long()
    end_val = model[e].as_long()
    print(f"{day} {{{fmt(start_val)}:{fmt(end_val)}}}")
else:
    print("No feasible meeting time found.")