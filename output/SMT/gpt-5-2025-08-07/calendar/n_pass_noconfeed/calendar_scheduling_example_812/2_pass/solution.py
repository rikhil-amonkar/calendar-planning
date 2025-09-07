from z3 import *

# Meeting parameters
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday"]
day = Int("day")        # 0=Mon, 1=Tue, 2=Wed, 3=Thu
start = Int("start")    # minutes from 09:00 (workday start)
dur = 30                # meeting duration in minutes
work_start = 0          # 09:00 -> 0
work_end = 480          # 17:00 -> 480

# Helper: convert HH:MM to minutes from 09:00
def m(h, mm):
    return (h - 9) * 60 + mm

# Busy intervals per participant per day (times as minutes from 09:00)
# Mary
mary_busy = {
    0: [],  # Monday
    1: [(m(10,0), m(10,30)), (m(15,30), m(16,0))],                      # Tuesday
    2: [(m(9,30), m(10,0)), (m(15,0), m(15,30))],                       # Wednesday
    3: [(m(9,0), m(10,0)), (m(10,30), m(11,30))],                       # Thursday
}

# Alexis
alexis_busy = {
    0: [(m(9,0), m(10,0)), (m(10,30), m(12,0)), (m(12,30), m(16,30))],  # Monday
    1: [(m(9,0), m(10,0)), (m(10,30), m(11,30)), (m(12,0), m(15,30)), (m(16,0), m(17,0))],  # Tuesday
    2: [(m(9,0), m(11,0)), (m(11,30), m(17,0))],                        # Wednesday
    3: [(m(10,0), m(12,0)), (m(14,0), m(14,30)), (m(15,30), m(16,0)), (m(16,30), m(17,0))], # Thursday
}

# Build solver with optimization for earliest slot (earliest day, then earliest time)
opt = Optimize()

# Domain constraints
opt.add(day >= 0, day <= 3)
opt.add(start >= work_start, start + dur <= work_end)
opt.add(start % 30 == 0)  # align to 30-minute slots

# Non-overlap constraints for Mary
for d in range(4):
    for (bs, be) in mary_busy.get(d, []):
        opt.add(Implies(day == d, Or(start + dur <= bs, start >= be)))

# Non-overlap constraints for Alexis
for d in range(4):
    for (bs, be) in alexis_busy.get(d, []):
        opt.add(Implies(day == d, Or(start + dur <= bs, start >= be)))

# Objective: earliest availability (prioritize earlier day, then earlier start)
opt.minimize(day * 10000 + start)

if opt.check() == sat:
    mdl = opt.model()
    d_val = mdl[day].as_long()
    s_val = mdl[start].as_long()
    e_val = s_val + dur

    def fmt(t):
        hh = 9 + t // 60
        mm = t % 60
        return f"{hh:02d}:{mm:02d}"

    print(f"{DAYS[d_val]} {{{fmt(s_val)}:{fmt(e_val)}}}")
else:
    print("No feasible meeting time found.")