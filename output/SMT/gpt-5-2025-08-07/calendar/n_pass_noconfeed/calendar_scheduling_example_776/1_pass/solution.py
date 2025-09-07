# Requires: z3-solver
# pip install z3-solver

from z3 import *

# Time helpers
def hhmm_to_min(h, m): 
    return h*60 + m

def min_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Constants
DAYS = ["Monday", "Tuesday", "Wednesday"]
MON, TUE, WED = 0, 1, 2
WORK_START = hhmm_to_min(9, 0)
WORK_END   = hhmm_to_min(17, 0)
DUR = 30  # 30 minutes
PREF_MONDAY_LATEST_END = hhmm_to_min(14, 30)  # John prefers to finish by 14:30 on Monday

# Participants' busy schedules per day (start, end) in minutes from midnight
# John: no fixed meetings
# Jennifer:
busy = {
    MON: [
        (hhmm_to_min(9, 0),  hhmm_to_min(11, 0)),
        (hhmm_to_min(11,30), hhmm_to_min(13, 0)),
        (hhmm_to_min(13,30), hhmm_to_min(14,30)),
        (hhmm_to_min(15, 0), hhmm_to_min(17, 0)),
    ],
    TUE: [
        (hhmm_to_min(9, 0),  hhmm_to_min(11,30)),
        (hhmm_to_min(12, 0), hhmm_to_min(17, 0)),
    ],
    WED: [
        (hhmm_to_min(9, 0),  hhmm_to_min(11,30)),
        (hhmm_to_min(12, 0), hhmm_to_min(12,30)),
        (hhmm_to_min(13, 0), hhmm_to_min(14, 0)),
        (hhmm_to_min(14,30), hhmm_to_min(16, 0)),
        (hhmm_to_min(16,30), hhmm_to_min(17, 0)),
    ],
}

# Z3 variables
day   = Int('day')      # 0=Monday, 1=Tuesday, 2=Wednesday
start = Int('start')    # start time in minutes from midnight
end_t = Int('end')      # end time in minutes from midnight

opt = Optimize()

# Domain constraints
opt.add(day >= 0, day <= 2)
opt.add(start >= WORK_START)
opt.add(end_t == start + DUR)
opt.add(end_t <= WORK_END)

# Align meeting to 30-minute boundary for clean times
opt.add(start % 30 == 0)

# No overlap with Jennifer's busy times depending on the day
for d in [MON, TUE, WED]:
    for (bs, be) in busy[d]:
        # If meeting is on day d, it must not overlap [bs, be)
        opt.add(Implies(day == d, Or(end_t <= bs, start >= be)))

# John's preference: avoid Monday meetings that go past 14:30
opt.add(Implies(day == MON, end_t <= PREF_MONDAY_LATEST_END))

# Preference: choose the earliest feasible day and earliest time in that day
opt.minimize(day)
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    d_val = m[day].as_long()
    s_val = m[start].as_long()
    e_val = m[end_t].as_long()
    day_name = DAYS[d_val]
    print(day_name, "{" + f"{min_to_hhmm(s_val)}:{min_to_hhmm(e_val)}" + "}")
else:
    print("No solution found")