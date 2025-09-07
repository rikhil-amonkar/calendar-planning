from z3 import *

# Time helpers
def to_minutes(h, m):
    return h * 60 + m

def fmt(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Meeting parameters
duration = 60  # minutes
work_start = to_minutes(9, 0)
work_end = to_minutes(17, 0)

# Busy schedules in minutes per day index: 0=Mon, 1=Tue, 2=Wed, 3=Thu
# Intervals are [start, end) in minutes after midnight
Carl_busy = {
    0: [(to_minutes(11,0), to_minutes(11,30))],
    1: [(to_minutes(14,30), to_minutes(15,0))],
    2: [(to_minutes(10,0), to_minutes(11,30)),
        (to_minutes(13,0), to_minutes(13,30))],
    3: [(to_minutes(13,30), to_minutes(14,0)),
        (to_minutes(16,0), to_minutes(16,30))]
}

Margaret_busy = {
    0: [(to_minutes(9,0), to_minutes(10,30)),
        (to_minutes(11,0), to_minutes(17,0))],
    1: [(to_minutes(9,30), to_minutes(12,0)),
        (to_minutes(13,30), to_minutes(14,0)),
        (to_minutes(15,30), to_minutes(17,0))],
    2: [(to_minutes(9,30), to_minutes(12,0)),
        (to_minutes(12,30), to_minutes(13,0)),
        (to_minutes(13,30), to_minutes(14,30)),
        (to_minutes(15,0), to_minutes(17,0))],
    3: [(to_minutes(10,0), to_minutes(12,0)),
        (to_minutes(12,30), to_minutes(14,0)),
        (to_minutes(14,30), to_minutes(17,0))]
}

# Z3 variables
day = Int('day')        # 0..3 for Monday..Thursday
start = Int('start')    # start time in minutes from 00:00

# Derived end time
end = start + duration

opt = Optimize()

# Domain constraints
opt.add(day >= 0, day <= 3)
opt.add(start >= work_start, end <= work_end)

# No-overlap constraints for each participant based on selected day
for d in range(4):
    for (bs, be) in Carl_busy.get(d, []):
        opt.add(Implies(day == d, Or(end <= bs, start >= be)))
    for (bs, be) in Margaret_busy.get(d, []):
        opt.add(Implies(day == d, Or(end <= bs, start >= be)))

# Preference: avoid Thursday (day == 3)
opt.minimize(If(day == 3, 1, 0))
# Tie-breakers: earlier in the week, then earlier in the day
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = s_val + duration
    print(days[d_val])
    print("{" + f"{fmt(s_val)}:{fmt(e_val)}" + "}")
else:
    print("No feasible meeting time found.")