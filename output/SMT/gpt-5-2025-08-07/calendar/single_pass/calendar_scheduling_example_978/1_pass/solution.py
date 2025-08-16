from z3 import *

def t(h, m):
    return h * 60 + m

# Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Busy schedules as minutes within the day [start, end)
brian_busy = {
    0: [(t(9,30), t(10,0)), (t(12,30), t(14,30)), (t(15,30), t(16,0))],
    1: [(t(9,0), t(9,30))],
    2: [(t(12,30), t(14,0)), (t(16,30), t(17,0))],
    3: [(t(11,0), t(11,30)), (t(13,0), t(13,30)), (t(16,30), t(17,0))],
    4: [(t(9,30), t(10,0)), (t(10,30), t(11,0)), (t(13,0), t(13,30)), (t(15,0), t(16,0)), (t(16,30), t(17,0))]
}

julia_busy = {
    0: [(t(9,0), t(10,0)), (t(11,0), t(11,30)), (t(12,30), t(13,0)), (t(15,30), t(16,0))],
    1: [(t(13,0), t(14,0)), (t(16,0), t(16,30))],
    2: [(t(9,0), t(11,30)), (t(12,0), t(12,30)), (t(13,0), t(17,0))],
    3: [(t(9,0), t(10,30)), (t(11,0), t(17,0))],
    4: [(t(9,0), t(10,0)), (t(10,30), t(11,30)), (t(12,30), t(14,0)), (t(14,30), t(15,0)), (t(15,30), t(16,0))]
}

# Z3 variables
day = Int('day')               # 0..4
start = Int('start')           # minutes within the day [540, 960]
duration = 60
end = start + duration

o = Optimize()

# Domain constraints
o.add(And(day >= 0, day <= 4))
o.add(start >= t(9,0))             # Earliest start 09:00
o.add(end <= t(17,0))              # Latest end 17:00

# No overlap with busy schedules
def no_overlap_for(person_busy):
    for d in range(5):
        for (bs, be) in person_busy[d]:
            # If on day d, then meeting must be entirely before or after the busy interval
            o.add(Implies(day == d, Or(end <= bs, start >= be)))

no_overlap_for(brian_busy)
no_overlap_for(julia_busy)

# Preferences:
# 1) Avoid Monday if possible
is_monday = If(day == 0, 1, 0)
o.minimize(is_monday)
# 2) Earliest day (Tuesday earliest among non-Monday if possible)
o.minimize(day)
# 3) Earliest time within the chosen day
o.minimize(start)

# Solve
if o.check() != sat:
    raise RuntimeError("No solution found, but one was expected.")

m = o.model()
sel_day = m[day].as_long()
sel_start = m[start].as_long()
sel_end = sel_start + duration

def fmt_time(total_minutes):
    h = total_minutes // 60
    mnt = total_minutes % 60
    return f"{h:02d}:{mnt:02d}"

print("SOLUTION:")
print(f"Day: {days[sel_day]}")
print(f"Start Time: {fmt_time(sel_start)}")
print(f"End Time: {fmt_time(sel_end)}")