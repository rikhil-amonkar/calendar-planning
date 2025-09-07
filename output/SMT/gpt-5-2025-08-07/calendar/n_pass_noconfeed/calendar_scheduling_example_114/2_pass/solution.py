from z3 import Optimize, Int, Or, sat

def to_min(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def add_no_overlap(opt, start, end, intervals):
    # Enforce [start, end) does not intersect any [a, b)
    for a, b in intervals:
        opt.add(Or(end <= a, start >= b))

# Workday and meeting info
day = "Monday"
work_start = to_min("09:00")
work_end = to_min("17:00")
duration = 60

# Busy schedules (inclusive of start, exclusive of end)
stephanie_busy = [
    (to_min("10:00"), to_min("10:30")),
    (to_min("16:00"), to_min("16:30")),
]

cheryl_busy = [
    (to_min("10:00"), to_min("10:30")),
    (to_min("11:30"), to_min("12:00")),
    (to_min("13:30"), to_min("14:00")),
    (to_min("16:30"), to_min("17:00")),
]

bradley_busy = [
    (to_min("09:30"), to_min("10:00")),
    (to_min("10:30"), to_min("11:30")),
    (to_min("13:30"), to_min("14:00")),
    (to_min("14:30"), to_min("15:00")),
    (to_min("15:30"), to_min("17:00")),
]

steven_busy = [
    (to_min("09:00"), to_min("12:00")),
    (to_min("13:00"), to_min("13:30")),
    (to_min("14:30"), to_min("17:00")),
]

# SMT model
opt = Optimize()
start = Int("start")
end = start + duration

# Working hours constraints
opt.add(start >= work_start, end <= work_end)

# No-overlap constraints for each participant
add_no_overlap(opt, start, end, stephanie_busy)
add_no_overlap(opt, start, end, cheryl_busy)
add_no_overlap(opt, start, end, bradley_busy)
add_no_overlap(opt, start, end, steven_busy)

# Prefer earliest feasible start
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    st = m[start].as_long()
    en = st + duration
    print(f"{day}{{{fmt(st)}:{fmt(en)}}}")
else:
    print("No feasible time found.")