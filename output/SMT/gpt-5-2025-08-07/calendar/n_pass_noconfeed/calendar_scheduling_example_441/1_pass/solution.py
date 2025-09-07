from z3 import *

# Helper functions
def hm(h, m):
    return h * 60 + m

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Problem setup
day = "Monday"
work_start = hm(9, 0)
work_end = hm(17, 0)
duration = 30  # minutes

# Busy schedules (start, end) in minutes since 00:00
schedules = {
    "Joan":    [(hm(11,30), hm(12, 0)), (hm(14,30), hm(15, 0))],
    "Megan":   [(hm(9, 0),  hm(10, 0)), (hm(14, 0), hm(14,30)), (hm(16, 0), hm(16,30))],
    "Austin":  [],  # free all day
    "Betty":   [(hm(9,30), hm(10, 0)), (hm(11,30),hm(12, 0)), (hm(13,30),hm(14, 0)), (hm(16, 0),hm(16,30))],
    "Judith":  [(hm(9, 0), hm(11, 0)), (hm(12, 0),hm(13, 0)), (hm(14, 0),hm(15, 0))],
    "Terry":   [(hm(9,30), hm(10, 0)), (hm(11,30),hm(12,30)), (hm(13, 0),hm(14, 0)), (hm(15, 0),hm(15,30)), (hm(16, 0),hm(17, 0))],
    "Kathryn": [(hm(9,30), hm(10, 0)), (hm(10,30),hm(11, 0)), (hm(11,30),hm(13, 0)), (hm(14, 0),hm(16, 0)), (hm(16,30),hm(17, 0))],
}

# Z3 variables
start = Int('start')
end = start + duration

s = Solver()
s.add(start >= work_start, end <= work_end)

# Non-overlap constraints for each participant's busy intervals
for person, busy_list in schedules.items():
    for (b_start, b_end) in busy_list:
        # Meeting [start, end) must not intersect busy [b_start, b_end)
        s.add(Or(end <= b_start, start >= b_end))

# Solve
if s.check() == sat:
    m = s.model()
    start_min = m[start].as_long()
    end_min = start_min + duration
    print(day)
    print(f"{{{fmt(start_min)}:{fmt(end_min)}}}")
else:
    print("No feasible time found.")