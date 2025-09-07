from z3 import Optimize, Int, Or, And, sat

def minutes(h, m=0):
    return h * 60 + m

def fmt(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
DAY = "Monday"
WORK_START = minutes(9, 0)
WORK_END = minutes(17, 0)
DURATION = 30

# Busy intervals are [start, end) in minutes from midnight
busy = {
    "Natalie": [],
    "David": [
        (minutes(11,30), minutes(12,0)),
        (minutes(14,30), minutes(15,0)),
    ],
    "Douglas": [
        (minutes(9,30), minutes(10,0)),
        (minutes(11,30), minutes(12,0)),
        (minutes(13,0), minutes(13,30)),
        (minutes(14,30), minutes(15,0)),
    ],
    "Ralph": [
        (minutes(9,0), minutes(9,30)),
        (minutes(10,0), minutes(11,0)),
        (minutes(11,30), minutes(12,30)),
        (minutes(13,30), minutes(15,0)),
        (minutes(15,30), minutes(16,0)),
        (minutes(16,30), minutes(17,0)),
    ],
    "Jordan": [
        (minutes(9,0), minutes(10,0)),
        (minutes(12,0), minutes(12,30)),
        (minutes(13,0), minutes(13,30)),
        (minutes(14,30), minutes(15,0)),
        (minutes(15,30), minutes(17,0)),
    ],
}

# Preference: David does not want to meet before 14:00 on Monday
PREF_DAVID_NOT_BEFORE = minutes(14, 0)

opt = Optimize()
start = Int("start")
end = Int("end")

# Basic constraints
opt.add(end == start + DURATION)
opt.add(start >= WORK_START, end <= WORK_END)

# Apply David's preference
opt.add(start >= PREF_DAVID_NOT_BEFORE)

# No-overlap constraints for each participant
def no_overlap(s, e, intervals):
    return And([Or(end <= bs, start >= be) for (bs, be) in intervals]) if intervals else And(True)

for person, intervals in busy.items():
    opt.add(no_overlap(start, end, intervals))

# Prefer earliest feasible start time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s_val = model[start].as_long()
    e_val = model[end].as_long()
    print(DAY)
    print(f"{{{fmt(s_val)}:{fmt(e_val)}}}")
else:
    print("No feasible time found.")