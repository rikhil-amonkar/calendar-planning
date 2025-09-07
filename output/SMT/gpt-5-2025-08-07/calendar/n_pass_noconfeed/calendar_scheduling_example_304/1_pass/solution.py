from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Problem parameters
day = "Monday"
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 30  # minutes

# Busy schedules (inclusive of start, exclusive of end)
busy = {
    "Christine": [
        (minutes(9,30), minutes(10,30)),
        (minutes(12,0), minutes(12,30)),
        (minutes(13,0), minutes(13,30)),
        (minutes(14,30), minutes(15,0)),
        (minutes(16,0), minutes(16,30)),
    ],
    "Janice": [
        # Janice's calendar is wide open; preference handled as soft constraint
    ],
    "Bobby": [
        (minutes(12,0), minutes(12,30)),
        (minutes(14,30), minutes(15,0)),
    ],
    "Elizabeth": [
        (minutes(9,0), minutes(9,30)),
        (minutes(11,30), minutes(13,0)),
        (minutes(13,30), minutes(14,0)),
        (minutes(15,0), minutes(15,30)),
        (minutes(16,0), minutes(17,0)),
    ],
    "Tyler": [
        (minutes(9,0), minutes(11,0)),
        (minutes(12,0), minutes(12,30)),
        (minutes(13,0), minutes(13,30)),
        (minutes(15,30), minutes(16,0)),
        (minutes(16,30), minutes(17,0)),
    ],
    "Edward": [
        (minutes(9,0), minutes(9,30)),
        (minutes(10,0), minutes(11,0)),
        (minutes(11,30), minutes(14,0)),
        (minutes(14,30), minutes(15,30)),
        (minutes(16,0), minutes(17,0)),
    ],
}

# SMT model
opt = Optimize()
start = Int("start")

# Working hours constraint
opt.add(start >= work_start)
opt.add(start + duration <= work_end)

# No-overlap constraints for all participants
for person, intervals in busy.items():
    for (b_start, b_end) in intervals:
        # Meeting ends before busy starts OR starts after busy ends
        opt.add(Or(start + duration <= b_start, start >= b_end))

# Preference: Janice would rather not meet after 13:00 (soft constraint)
janice_pref_end = minutes(13, 0)
opt.add_soft(start + duration <= janice_pref_end, weight="1", id="janice_pref_before_13")

# Tie-breaker: choose earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s_val = model.evaluate(start).as_long()
    e_val = s_val + duration
    print(day)
    print("{" + f"{fmt_time(s_val)}:{fmt_time(e_val)}" + "}")
else:
    print("No feasible meeting time found.")