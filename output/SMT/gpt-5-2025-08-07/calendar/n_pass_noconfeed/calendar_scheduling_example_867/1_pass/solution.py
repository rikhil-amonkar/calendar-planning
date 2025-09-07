from z3 import *

# Helpers
def t(h, m):  # minutes from midnight
    return h * 60 + m

def add_no_overlap_constraints(opt, day_var, start_var, busy_by_day, day_idx):
    # For each busy interval [a,b) on this day, assert the meeting [start, start+30) does not overlap it
    for (a, b) in busy_by_day.get(day_idx, []):
        opt.add(Implies(day_var == day_idx, Or(start_var + 30 <= a, start_var >= b)))

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
MON, TUE, WED, THU = 0, 1, 2, 3

# Busy schedules (minutes from midnight)
betty_busy = {
    MON: [(t(10,0), t(10,30)), (t(13,30), t(14,0)), (t(15,0), t(15,30)), (t(16,0), t(16,30))],
    TUE: [(t(9,0), t(9,30)), (t(11,30), t(12,0)), (t(12,30), t(13,0)), (t(13,30), t(14,0)), (t(16,30), t(17,0))],
    WED: [(t(9,30), t(10,30)), (t(13,0), t(13,30)), (t(14,0), t(14,30))],
    THU: [(t(9,30), t(10,0)), (t(11,30), t(12,0)), (t(14,0), t(14,30)), (t(15,0), t(15,30)), (t(16,30), t(17,0))]
}

scott_busy = {
    MON: [(t(9,30), t(15,0)), (t(15,30), t(16,0)), (t(16,30), t(17,0))],
    TUE: [(t(9,0), t(9,30)), (t(10,0), t(11,0)), (t(11,30), t(12,0)), (t(12,30), t(13,30)), (t(14,0), t(15,0)), (t(16,0), t(16,30))],
    WED: [(t(9,30), t(12,30)), (t(13,0), t(13,30)), (t(14,0), t(14,30)), (t(15,0), t(15,30)), (t(16,0), t(16,30))],
    THU: [(t(9,0), t(9,30)), (t(10,0), t(10,30)), (t(11,0), t(12,0)), (t(12,30), t(13,0)), (t(15,0), t(16,0)), (t(16,30), t(17,0))]
}

# Variables
day = Int('day')         # 0..3  (Mon..Thu)
slot = Int('slot')       # 0..15 (30-min slots from 09:00 to 16:30)
start = Int('start')     # minutes from midnight
end = Int('end')         # start + 30

opt = Optimize()

# Domains and relations
opt.add(day >= MON, day <= THU)
opt.add(slot >= 0, slot <= 15)
opt.add(start == t(9,0) + 30*slot)
opt.add(end == start + 30)

# Working hours constraint: 09:00 to 17:00
opt.add(start >= t(9,0))
opt.add(end <= t(17,0))

# No-overlap constraints for each participant per day
for d in [MON, TUE, WED, THU]:
    add_no_overlap_constraints(opt, day, start, betty_busy, d)
    add_no_overlap_constraints(opt, day, start, scott_busy, d)

# Additional constraints/preferences:
# "Betty can not meet on Monday. Tuesday. Thursday before 15:00."
opt.add(day != MON)  # cannot meet on Monday
opt.add(day != TUE)  # cannot meet on Tuesday
opt.add(Implies(day == THU, start >= t(15,0)))  # Thursday before 15:00 is not allowed

# "Scott would like to avoid more meetings on Wednesday." (soft constraint)
opt.add_soft(day != WED, weight='1', id='avoid_wednesday')

# Additionally, prefer the earliest feasible time (soft objective by minimizing slot)
opt.minimize(slot)

# Solve
if opt.check() == sat:
    m = opt.model()
    d_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = m[end].as_long()

    def fmt(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    day_str = days[d_val]
    start_str = fmt(start_val)
    end_str = fmt(end_val)

    # Output day and time range in required format
    print(day_str)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No feasible meeting time found.")