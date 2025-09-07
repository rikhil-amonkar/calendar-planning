from z3 import Optimize, Int, Or, sat

# Helper to convert hour/minute to minutes since midnight
def minutes(h, m):
    return h * 60 + m

# Helper to format minutes since midnight as HH:MM
def fmt(mins):
    return f"{mins // 60:02d}:{mins % 60:02d}"

# Work day and meeting settings
DAY = "Monday"
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 30  # minutes

# Busy intervals for each participant on Monday, as (start_min, end_min), end-exclusive
michael_busy = [
    (minutes(9, 30), minutes(10, 30)),
    (minutes(15, 0), minutes(15, 30)),
    (minutes(16, 0), minutes(16, 30)),
]
eric_busy = [
    # Eric is free all day; no busy intervals
]
arthur_busy = [
    (minutes(9, 0), minutes(12, 0)),
    (minutes(13, 0), minutes(15, 0)),
    (minutes(15, 30), minutes(16, 0)),
    (minutes(16, 30), minutes(17, 0)),
]

# Create optimizer to find the earliest valid start time
opt = Optimize()
start = Int("start")

# Meeting must be within work hours
opt.add(start >= work_start)
opt.add(start + duration <= work_end)

# No overlap constraints: for each busy interval [s,e), require meeting end <= s or start >= e
def add_no_overlap(busy_intervals):
    for s_i, e_i in busy_intervals:
        opt.add(Or(start + duration <= s_i, start >= e_i))

add_no_overlap(michael_busy)
add_no_overlap(eric_busy)
add_no_overlap(arthur_busy)

# Minimize the start time to get the earliest feasible slot
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    st = model[start].as_long()
    en = st + duration
    # Output must include the day and the time range in {HH:MM:HH:MM}
    print(f"{DAY} {{{fmt(st)}:{fmt(en)}}}")
else:
    print("No feasible meeting time found.")