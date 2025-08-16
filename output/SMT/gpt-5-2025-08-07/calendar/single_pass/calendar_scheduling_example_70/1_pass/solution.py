# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, And, Or, sat

def hm_to_minutes(h, m):
    return h * 60 + m

def minutes_to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Problem data
day = "Monday"
work_start = hm_to_minutes(9, 0)
work_end   = hm_to_minutes(17, 0)
duration = 30  # minutes

# Busy intervals are half-open [start, end)
# Denise busy: 12:00-12:30, 15:30-16:00
denise_busy = [
    (hm_to_minutes(12, 0), hm_to_minutes(12, 30)),
    (hm_to_minutes(15, 30), hm_to_minutes(16, 0)),
]

# Angela: no meetings
angela_busy = []

# Natalie busy: 9:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00
natalie_busy = [
    (hm_to_minutes(9, 0),  hm_to_minutes(11, 30)),
    (hm_to_minutes(12, 0), hm_to_minutes(13, 0)),
    (hm_to_minutes(14, 0), hm_to_minutes(14, 30)),
    (hm_to_minutes(15, 0), hm_to_minutes(17, 0)),
]

participants_busy = denise_busy + angela_busy + natalie_busy

# Z3 model
opt = Optimize()
s = Int("start")  # start time in minutes from 00:00
e = Int("end")

# Meeting duration and within work hours
opt.add(e == s + duration)
opt.add(s >= work_start)
opt.add(e <= work_end)

# No overlap with any busy interval: [s,e) does not intersect [a,b)
for (a, b) in participants_busy:
    opt.add(Or(e <= a, s >= b))

# Earliest availability
opt.minimize(s)

if opt.check() == sat:
    m = opt.model()
    start_min = m[s].as_long()
    end_min = start_min + duration

    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_hhmm(start_min)} (24-hour format)")
    print(f"End Time: {minutes_to_hhmm(end_min)} (24-hour format)")
else:
    print("No solution found.")