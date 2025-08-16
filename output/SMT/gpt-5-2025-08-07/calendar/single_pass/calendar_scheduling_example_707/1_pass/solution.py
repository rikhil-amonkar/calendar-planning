# Requires: z3-solver
# pip install z3-solver

from z3 import Optimize, Int, And, Or, Not, Implies

# Constants
MON, TUE, WED = 0, 1, 2
WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes
DURATION = 30         # 30 minutes
WORK_BLOCK = WORK_END - WORK_START  # 480 minutes
PREF_CUTOFF_MON = (14 * 60 + 30) - WORK_START  # minutes since 09:00 => 330

# Busy intervals are represented in minutes relative to 09:00 (i.e., 09:00 => 0).
# Helper to convert an absolute HH:MM to minutes relative to 09:00.
def rel(h, m):
    return h * 60 + m - WORK_START

# Schedules
# Ryan
ryan_busy = {
    MON: [(rel(9,30), rel(10,0)), (rel(11,0), rel(12,0)), (rel(13,0), rel(13,30)), (rel(15,30), rel(16,0))],
    TUE: [(rel(11,30), rel(12,30)), (rel(15,30), rel(16,0))],
    WED: [(rel(12,0), rel(13,0)), (rel(15,30), rel(16,0)), (rel(16,30), rel(17,0))]
}

# Adam
adam_busy = {
    MON: [(rel(9,0), rel(10,30)), (rel(11,0), rel(13,30)), (rel(14,0), rel(16,0)), (rel(16,30), rel(17,0))],
    TUE: [(rel(9,0), rel(10,0)), (rel(10,30), rel(15,30)), (rel(16,0), rel(17,0))],
    WED: [(rel(9,0), rel(9,30)), (rel(10,0), rel(11,0)), (rel(11,30), rel(14,30)), (rel(15,0), rel(15,30)), (rel(16,0), rel(16,30))]
}

# Decision variables
opt = Optimize()
day = Int('day')              # 0=Mon, 1=Tue, 2=Wed
start = Int('start')          # minutes since 09:00
end = Int('end')

# Domains
opt.add(day >= MON, day <= WED)
opt.add(start >= 0, end == start + DURATION, end <= WORK_BLOCK)

# Hard constraints
# Ryan cannot meet on Wednesday
opt.add(day != WED)

# No overlap with busy schedules
def no_overlap_for(person_busy):
    for d in [MON, TUE, WED]:
        for (bs, be) in person_busy[d]:
            # If chosen day is d, meeting [start,end) must not overlap [bs,be)
            opt.add(Implies(day == d, Or(end <= bs, start >= be)))

no_overlap_for(ryan_busy)
no_overlap_for(adam_busy)

# Soft preferences:
# 1) Adam would like to avoid Monday meetings before 14:30
opt.add_soft(Not(And(day == MON, start < PREF_CUTOFF_MON)), weight=1)
# 2) Prefer Tuesday if possible
opt.add_soft(day == TUE, weight=1)

# Among equally preferred options, choose the earliest time
opt.minimize(start)

# Solve
if opt.check() != 1:  # 1 == sat
    raise RuntimeError("No solution found, but the problem statement guarantees one exists.")

m = opt.model()
d = m[day].as_long()
s = m[start].as_long()
e = s + DURATION

# Convert back to clock times
def to_hhmm(minutes_since_9):
    total = WORK_START + minutes_since_9
    h = total // 60
    mm = total % 60
    return f"{h:02d}:{mm:02d}"

day_name = {MON: "Monday", TUE: "Tuesday", WED: "Wednesday"}[d]
start_str = to_hhmm(s)
end_str = to_hhmm(e)

print("SOLUTION:")
print(f"Day: {day_name}")
print(f"Start Time: {start_str}")
print(f"End Time: {end_str}")