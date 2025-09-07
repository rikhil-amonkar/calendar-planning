import z3

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Problem data
day = "Monday"
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 30  # minutes

# Busy intervals (absolute minutes since midnight)
busy = {
    "John": [
        (minutes(11, 30), minutes(12, 0)),
        (minutes(14, 0), minutes(14, 30)),
    ],
    "Megan": [
        (minutes(12, 0), minutes(12, 30)),
        (minutes(14, 0), minutes(15, 0)),
        (minutes(15, 30), minutes(16, 0)),
    ],
    "Brandon": [
        # No meetings
    ],
    "Kimberly": [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(10, 0), minutes(10, 30)),
        (minutes(11, 0), minutes(14, 30)),
        (minutes(15, 0), minutes(16, 0)),
        (minutes(16, 30), minutes(17, 0)),
    ],
    "Sean": [
        (minutes(10, 0), minutes(11, 0)),
        (minutes(11, 30), minutes(14, 0)),
        (minutes(15, 0), minutes(15, 30)),
    ],
    "Lori": [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(10, 30), minutes(12, 0)),
        (minutes(13, 0), minutes(14, 30)),
        (minutes(16, 0), minutes(16, 30)),
    ],
}

# Z3 model
opt = z3.Optimize()
s = z3.Int("start")  # meeting start time in minutes since midnight
e = s + duration

# Working hours and 30-minute grid alignment
opt.add(s >= work_start, e <= work_end, s % 30 == 0)

# Non-overlap constraints
for person, intervals in busy.items():
    for (b_start, b_end) in intervals:
        opt.add(z3.Or(e <= b_start, s >= b_end))

# Find earliest feasible start
opt.minimize(s)

if opt.check() == z3.sat:
    m = opt.model()
    start = m.evaluate(s).as_long()
    end = start + duration
    print(f"{day} {{{fmt_time(start)}:{fmt_time(end)}}}")
else:
    print("No feasible meeting time found.")