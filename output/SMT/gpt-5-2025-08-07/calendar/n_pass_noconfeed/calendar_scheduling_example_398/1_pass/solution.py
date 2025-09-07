from z3 import *

def t(h, m):  # minutes since midnight
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Problem parameters
day = "Monday"
work_start = t(9, 0)
work_end = t(17, 0)
duration = 30  # minutes

# Blocked intervals [start, end) in minutes since midnight
blocked = {
    "Doris": [
        (t(9, 0),  t(11, 0)),
        (t(13, 30), t(14, 0)),
        (t(16, 0), t(16, 30)),
    ],
    "Theresa": [
        (t(10, 0), t(12, 0)),
    ],
    "Christian": [
        # No meetings
    ],
    "Terry": [
        (t(9, 30),  t(10, 0)),
        (t(11, 30), t(12, 0)),
        (t(12, 30), t(13, 0)),
        (t(13, 30), t(14, 0)),
        (t(14, 30), t(15, 0)),
        (t(15, 30), t(17, 0)),
    ],
    "Carolyn": [
        (t(9, 0),  t(10, 30)),
        (t(11, 0), t(11, 30)),
        (t(12, 0), t(13, 0)),
        (t(13, 30), t(14, 30)),
        (t(15, 0),  t(17, 0)),
    ],
    "Kyle": [
        (t(9, 0),  t(9, 30)),
        (t(11, 30), t(12, 0)),
        (t(12, 30), t(13, 0)),
        (t(14, 30), t(17, 0)),
    ],
}

# Z3 model
start = Int('start')
opt = Optimize()

# Working hours and duration
opt.add(start >= work_start)
opt.add(start + duration <= work_end)

# No overlap with any blocked interval
for person, intervals in blocked.items():
    for (bs, be) in intervals:
        # Meeting [start, start+duration) does not intersect [bs, be)
        opt.add(Or(start >= be, start + duration <= bs))

# Optionally, find the earliest feasible meeting time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    s = m[start].as_long()
    e = s + duration
    print(day)
    print("{" + f"{fmt(s)}:{fmt(e)}" + "}")
else:
    print(day)
    print("{No feasible time}")