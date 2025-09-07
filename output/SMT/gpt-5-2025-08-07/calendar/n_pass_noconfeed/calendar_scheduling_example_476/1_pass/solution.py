# Requires: z3-solver (pip install z3-solver)
from z3 import *

def hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Time helpers
def to_min(h, m):
    return h * 60 + m

# Problem data
day = "Monday"
work_start = to_min(9, 0)
work_end   = to_min(17, 0)
duration   = 30  # minutes

# Busy intervals per participant on Monday: list of (start_min, end_min)
busy = {
    "Daniel": [],
    "Kathleen": [(to_min(14,30), to_min(15,30))],
    "Carolyn":  [(to_min(12, 0), to_min(12,30)), (to_min(13, 0), to_min(13,30))],
    "Roger":    [],  # preference handled separately
    "Cheryl":   [(to_min( 9, 0), to_min( 9,30)),
                 (to_min(10, 0), to_min(11,30)),
                 (to_min(12,30), to_min(13,30)),
                 (to_min(14, 0), to_min(17, 0))],
    "Virginia": [(to_min( 9,30), to_min(11,30)),
                 (to_min(12, 0), to_min(12,30)),
                 (to_min(13, 0), to_min(13,30)),
                 (to_min(14,30), to_min(15,30)),
                 (to_min(16, 0), to_min(17, 0))],
    "Angela":   [(to_min( 9,30), to_min(10, 0)),
                 (to_min(10,30), to_min(11,30)),
                 (to_min(12, 0), to_min(12,30)),
                 (to_min(13, 0), to_min(13,30)),
                 (to_min(14, 0), to_min(16,30))],
}

# Preference: Roger would rather not meet before 12:30 on Monday
roger_pref_start = to_min(12, 30)

# Z3 model
opt = Optimize()
opt.set(priority="lex")

start = Int("start")  # minutes from midnight
end   = Int("end")

# Core constraints
opt.add(start >= work_start)
opt.add(end == start + duration)
opt.add(end <= work_end)

# Schedule alignment to 30-minute slots
opt.add(start % 30 == 0)

# No-overlap constraints with each participant's busy times
for person, blocks in busy.items():
    for s, e in blocks:
        opt.add(Or(end <= s, start >= e))

# Preference as a soft constraint (satisfy if possible), then among those minimize start
opt.add_soft(start >= roger_pref_start, weight=1)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    s = m[start].as_long()
    e = m[end].as_long()
    # Output day and time range in required format
    print(day)
    print(f"{{{hhmm(s)}:{hhmm(e)}}}")
else:
    # Fallback (should not happen per problem statement)
    print(day)
    print("{No feasible time found}")