# Requires: z3-solver
from z3 import Int, Or, Optimize, sat

def to_min(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def add_no_overlap(slv, start_var, end_var, busy_start, busy_end):
    # Meeting [start_var, end_var) must not overlap busy [busy_start, busy_end)
    slv.add(Or(end_var <= busy_start, start_var >= busy_end))

day = "Monday"
work_start = to_min("09:00")
work_end   = to_min("17:00")
duration = 30  # minutes

S = Int("S")
E = Int("E")

opt = Optimize()
opt.add(E == S + duration)
opt.add(S >= work_start, E <= work_end)
# Align to 30-minute grid
opt.add(S % 30 == 0)

# Participants' busy times (Monday)
busy_intervals = []
# Shirley: 10:30-11:00, 12:00-12:30
busy_intervals += [(to_min("10:30"), to_min("11:00"))]
busy_intervals += [(to_min("12:00"), to_min("12:30"))]

# Jacob: 9:00-9:30, 10:00-10:30, 11:00-11:30, 12:30-13:30, 14:30-15:00
busy_intervals += [(to_min("09:00"), to_min("09:30"))]
busy_intervals += [(to_min("10:00"), to_min("10:30"))]
busy_intervals += [(to_min("11:00"), to_min("11:30"))]
busy_intervals += [(to_min("12:30"), to_min("13:30"))]
busy_intervals += [(to_min("14:30"), to_min("15:00"))]

# Stephen: 11:30-12:00, 12:30-13:00
busy_intervals += [(to_min("11:30"), to_min("12:00"))]
busy_intervals += [(to_min("12:30"), to_min("13:00"))]

# Margaret: 9:00-9:30, 10:30-12:30, 13:00-13:30, 15:00-15:30, 16:30-17:00
busy_intervals += [(to_min("09:00"), to_min("09:30"))]
busy_intervals += [(to_min("10:30"), to_min("12:30"))]
busy_intervals += [(to_min("13:00"), to_min("13:30"))]
busy_intervals += [(to_min("15:00"), to_min("15:30"))]
busy_intervals += [(to_min("16:30"), to_min("17:00"))]

# Mason: 9:00-10:00, 10:30-11:00, 11:30-12:30, 13:00-13:30, 14:00-14:30, 16:30-17:00
busy_intervals += [(to_min("09:00"), to_min("10:00"))]
busy_intervals += [(to_min("10:30"), to_min("11:00"))]
busy_intervals += [(to_min("11:30"), to_min("12:30"))]
busy_intervals += [(to_min("13:00"), to_min("13:30"))]
busy_intervals += [(to_min("14:00"), to_min("14:30"))]
busy_intervals += [(to_min("16:30"), to_min("17:00"))]

# Add no-overlap constraints
for bs, be in busy_intervals:
    add_no_overlap(opt, S, E, bs, be)

# Preference: Margaret does not want to meet before 14:30
opt.add(S >= to_min("14:30"))

# Find the earliest feasible slot satisfying all constraints
opt.minimize(S)

if opt.check() == sat:
    m = opt.model()
    s_val = m[S].as_long()
    e_val = m[E].as_long()
    print(f"{{{to_hhmm(s_val)}:{to_hhmm(e_val)}}}")
    print(day)
else:
    print("No feasible meeting time found.")