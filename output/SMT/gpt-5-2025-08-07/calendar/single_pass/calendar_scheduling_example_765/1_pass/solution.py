from z3 import *

# Constants
DAYS = ["Monday", "Tuesday", "Wednesday"]
MON, TUE, WED = 0, 1, 2
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes
DURATION = 30         # 30 minutes

# Busy schedules in minutes from 00:00 for each day
def t(h, m): return h * 60 + m

# Joshua's busy times
joshua_busy = {
    MON: [(t(15, 0), t(15, 30))],
    TUE: [(t(11, 30), t(12, 0)), (t(13, 0), t(13, 30)), (t(14, 30), t(15, 0))],
    WED: []
}

# Joyce's busy times
joyce_busy = {
    MON: [(t(9, 0), t(9, 30)), (t(10, 0), t(11, 0)), (t(11, 30), t(12, 30)),
          (t(13, 0), t(15, 0)), (t(15, 30), t(17, 0))],
    TUE: [(t(9, 0), t(17, 0))],
    WED: [(t(9, 0), t(9, 30)), (t(10, 0), t(11, 0)), (t(12, 30), t(15, 30)), (t(16, 0), t(16, 30))]
}

# Z3 variables
day = Int('day')       # 0=Mon,1=Tue,2=Wed
start = Int('start')   # start time in minutes from 00:00
end = Int('end')       # end time in minutes from 00:00

opt = Optimize()

# Domain constraints
opt.add(And(day >= 0, day <= 2))
opt.add(end == start + DURATION)
opt.add(And(start >= WORK_START, end <= WORK_END))
# align to 30-minute increments
opt.add(Mod(start, 30) == 0)

# No-overlap constraints for both participants per chosen day
def no_overlap_for_day(d, intervals):
    if not intervals:
        return True
    return And([Or(end <= s, start >= e) for (s, e) in intervals])

for d in [MON, TUE, WED]:
    opt.add(Implies(day == d, no_overlap_for_day(d, joshua_busy[d])))
    opt.add(Implies(day == d, no_overlap_for_day(d, joyce_busy[d])))

# Preferences (soft constraints)
# 1) Prefer Wednesday
opt.add_soft(day == WED, weight="10")
# 2) Joyce would rather not meet on Monday before 12:00
opt.add_soft(Or(day != MON, start >= t(12, 0)), weight="5")

# Solve
if opt.check() == sat:
    m = opt.model()
    dval = m[day].as_long()
    sval = m[start].as_long()
    eval_ = m[end].as_long()

    def fmt(minutes):
        h = minutes // 60
        mi = minutes % 60
        return f"{h:02d}:{mi:02d}"

    print("SOLUTION:")
    print(f"Day: {DAYS[dval]}")
    print(f"Start Time: {fmt(sval)}")
    print(f"End Time: {fmt(eval_)}")
else:
    print("SOLUTION:")
    print("Day: N/A")
    print("Start Time: N/A")
    print("End Time: N/A")