from z3 import *

# Time helpers
def m(h, mi):  # minutes since midnight
    return h * 60 + mi

def fmt(t):  # format minutes since midnight to HH:MM
    h = t // 60
    mi = t % 60
    return f"{h:02d}:{mi:02d}"

# Constants
MON, TUE, WED, THU, FRI = 0, 1, 2, 3, 4
DAY_NAMES = {MON: "Monday", TUE: "Tuesday", WED: "Wednesday", THU: "Thursday", FRI: "Friday"}
WORK_START = m(9, 0)
WORK_END = m(17, 0)
DURATION = 60  # minutes

# Busy schedules per participant
betty_busy = {
    MON: [(m(10,0), m(10,30)), (m(11,30), m(12,30)), (m(16,0), m(16,30))],
    TUE: [(m(9,30), m(10,0)), (m(10,30), m(11,0)), (m(12,0), m(12,30)),
          (m(13,30), m(15,0)), (m(16,30), m(17,0))],
    WED: [(m(13,30), m(14,0)), (m(14,30), m(15,0))],
    THU: [],
    FRI: [(m(9,0), m(10,0)), (m(11,30), m(12,0)), (m(12,30), m(13,0)), (m(14,30), m(15,0))]
}

megan_busy = {
    MON: [(m(9,0), m(17,0))],
    TUE: [(m(9,0), m(9,30)), (m(10,0), m(10,30)), (m(12,0), m(14,0)),
          (m(15,0), m(15,30)), (m(16,0), m(16,30))],
    WED: [(m(9,30), m(10,30)), (m(11,0), m(11,30)), (m(12,30), m(13,0)),
          (m(13,30), m(14,30)), (m(15,30), m(17,0))],
    THU: [(m(9,0), m(10,30)), (m(11,30), m(14,0)), (m(14,30), m(15,0)), (m(15,30), m(16,30))],
    FRI: [(m(9,0), m(17,0))]
}

# Z3 variables
day = Int('day')       # 0..4 for Monday..Friday
start = Int('start')   # minutes since midnight

opt = Optimize()

# Day bounds (work days)
opt.add(day >= MON, day <= FRI)

# Meeting within work hours
opt.add(start >= WORK_START)
opt.add(start + DURATION <= WORK_END)

# Betty cannot meet on Wednesday or Thursday
opt.add(day != WED, day != THU)

# No-overlap constraints for busy intervals (treat intervals as [start, end) )
def add_no_overlap(schedule):
    for d, intervals in schedule.items():
        for (s, e) in intervals:
            # If meeting is on day d, then [start, start+DURATION) must not intersect [s, e)
            opt.add(Implies(day == d, Or(start + DURATION <= s, start >= e)))

add_no_overlap(betty_busy)
add_no_overlap(megan_busy)

# Optional preference: earliest day, then earliest start time
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    d_val = model[day].as_long()
    s_val = model[start].as_long()
    e_val = s_val + DURATION
    day_name = DAY_NAMES[d_val]
    print(f"{day_name} {{{fmt(s_val)}:{fmt(e_val)}}}")
else:
    print("No solution found.")