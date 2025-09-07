# Requires: z3-solver (pip install z3-solver)
from z3 import *

def mins(h, m):
    return h * 60 + m

def fmt(min_total):
    h = min_total // 60
    m = min_total % 60
    return f"{h:02d}:{m:02d}"

# Time bounds and meeting duration
WORK_START = mins(9, 0)
WORK_END = mins(17, 0)
MEET_DUR = 30
PREF_CUTOFF = mins(14, 0)  # Doris would rather not meet after 14:00 on Monday

# Busy schedules (half-open intervals [start, end))
monday_busy = [
    # Jean: no Monday busy slots listed
    # Doris:
    (mins(9, 0),  mins(11, 30)),
    (mins(12, 0), mins(12, 30)),
    (mins(13, 30), mins(16, 0)),
    (mins(16, 30), mins(17, 0)),
]
tuesday_busy = [
    # Jean:
    (mins(11, 30), mins(12, 0)),
    (mins(16, 0),  mins(16, 30)),
    # Doris: entire day busy on Tuesday
    (mins(9, 0), mins(17, 0)),
]

opt = Optimize()

# Variables
day = Int('day')        # 0 = Monday, 1 = Tuesday
start = Int('start')    # minutes from midnight (within chosen day)
end = Int('end')

opt.add(day >= 0, day <= 1)
opt.add(end == start + MEET_DUR)

# Within work hours and aligned to 30-min grid
opt.add(start >= WORK_START)
opt.add(end <= WORK_END)
opt.add(start % 30 == 0)

# No-overlap helper
def no_overlap_conditional(condition, intervals):
    for (bs, be) in intervals:
        # Meeting [start, end) does not overlap [bs, be)
        opt.add(Implies(condition, Or(end <= bs, start >= be)))

# Apply constraints per day
no_overlap_conditional(day == 0, monday_busy)
no_overlap_conditional(day == 1, tuesday_busy)

# Preference: Doris prefers not meeting on Monday at or after 14:00
penalty = If(And(day == 0, start >= PREF_CUTOFF), 1, 0)
opt.minimize(penalty)
# Also choose the earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    chosen_day = model[day].as_long()
    s = model[start].as_long()
    e = s + MEET_DUR
    day_str = "Monday" if chosen_day == 0 else "Tuesday"

    print(day_str)
    print("{" + f"{fmt(s)}:{fmt(e)}" + "}")
else:
    print("No feasible meeting time found.")