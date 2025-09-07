# Requires: z3-solver (pip install z3-solver)
from z3 import *

# Time helpers
def to_min(hh_mm):
    hh, mm = map(int, hh_mm.split(":"))
    return hh * 60 + mm

def fmt(mins):
    hh = mins // 60
    mm = mins % 60
    return f"{hh:02d}:{mm:02d}"

# Problem setup
work_start = to_min("09:00")
work_end   = to_min("17:00")
duration   = 30  # minutes

# Days: 0=Monday, 1=Tuesday, 2=Wednesday
days = ["Monday", "Tuesday", "Wednesday"]

# Busy schedules per person per day (times in minutes from 00:00)
# Intervals are [start, end) half-open
susan_busy = {
    0: [(to_min("12:30"), to_min("13:00")),
        (to_min("13:30"), to_min("14:00"))],
    1: [(to_min("11:30"), to_min("12:00"))],
    2: [(to_min("09:30"), to_min("10:30")),
        (to_min("14:00"), to_min("14:30")),
        (to_min("15:30"), to_min("16:30"))],
}

sandra_busy = {
    0: [(to_min("09:00"), to_min("13:00")),
        (to_min("14:00"), to_min("15:00")),
        (to_min("16:00"), to_min("16:30"))],
    1: [(to_min("09:00"), to_min("09:30")),
        (to_min("10:30"), to_min("12:00")),
        (to_min("12:30"), to_min("13:30")),
        (to_min("14:00"), to_min("14:30")),
        (to_min("16:00"), to_min("17:00"))],
    2: [(to_min("09:00"), to_min("11:30")),
        (to_min("12:00"), to_min("12:30")),
        (to_min("13:00"), to_min("17:00"))],
}

# Variables
day = Int("day")
start = Int("start")
end = Int("end")

opt = Optimize()

# Domain constraints
opt.add(And(day >= 0, day <= 2))
opt.add(start >= work_start)
opt.add(end == start + duration)
opt.add(end <= work_end)

# No-overlap constraints helper
def no_overlap_with(day_idx, start_var, end_var, intervals):
    cons = []
    for (bs, be) in intervals:
        cons.append(Or(end_var <= bs, start_var >= be))
    # all busy intervals must not overlap
    return And(cons) if cons else True

# Apply no-overlap for each day/person
for d in range(3):
    opt.add(Implies(day == d, no_overlap_with(d, start, end, susan_busy[d])))
    opt.add(Implies(day == d, no_overlap_with(d, start, end, sandra_busy[d])))

# Additional constraint: Sandra cannot meet on Monday after 16:00
opt.add(Implies(day == 0, end <= to_min("16:00")))

# Preference: Susan would rather not meet on Tuesday (soft constraint)
opt.add_soft(day != 1, weight="10")

# Tie-breaker: choose the earliest feasible time-of-day
h1 = opt.minimize(start)

# Solve
if opt.check() == sat:
    m = opt.model()
    chosen_day = m[day].as_long()
    s = m[start].as_long()
    e = m[end].as_long()
    # Output: include both the time range and the day
    print(days[chosen_day])
    print("{" + f"{fmt(s)}:{fmt(e)}" + "}")
else:
    print("No feasible meeting time found.")