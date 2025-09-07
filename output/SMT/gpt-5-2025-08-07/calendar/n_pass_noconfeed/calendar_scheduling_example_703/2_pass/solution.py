from z3 import Optimize, Int, Or, Implies, sat

# Minutes helper: convert HH:MM to minutes from 09:00 (workday start)
def to_min(h, m):
    return (h - 9) * 60 + m

# Meeting parameters
MEETING_DURATION = 60  # minutes
WORK_START = 0         # 09:00 -> 0 minutes
WORK_END = 8 * 60      # 17:00 -> 480 minutes

# Days indexing
MON, TUE, WED = 0, 1, 2
day_names = ["Monday", "Tuesday", "Wednesday"]

# Busy schedules per participant per day (times are [start, end) in minutes from 09:00)
stephanie_busy = {
    MON: [
        (to_min(9,30),  to_min(10,0)),
        (to_min(10,30), to_min(11,0)),
        (to_min(11,30), to_min(12,0)),
        (to_min(14,0),  to_min(14,30)),
    ],
    TUE: [
        (to_min(12,0),  to_min(13,0)),
    ],
    WED: [
        (to_min(9,0),   to_min(10,0)),
        (to_min(13,0),  to_min(14,0)),
    ],
}

betty_busy = {
    MON: [
        (to_min(9,0),   to_min(10,0)),
        (to_min(11,0),  to_min(11,30)),
        (to_min(14,30), to_min(15,0)),
        (to_min(15,30), to_min(16,0)),
    ],
    TUE: [
        (to_min(9,0),   to_min(9,30)),
        (to_min(11,30), to_min(12,0)),
        (to_min(12,30), to_min(14,30)),
        (to_min(15,30), to_min(16,0)),
    ],
    WED: [
        (to_min(10,0),  to_min(11,30)),
        (to_min(12,0),  to_min(14,0)),
        (to_min(14,30), to_min(17,0)),
    ],
}

# SMT variables
opt = Optimize()
day = Int("day")
start = Int("start")
end = Int("end")

# Basic constraints
opt.add(day >= MON, day <= WED)
opt.add(start >= WORK_START, end == start + MEETING_DURATION, end <= WORK_END)

# Align to 30-minute boundaries
opt.add(start % 30 == 0)

# No overlap helper
def no_overlap(start_var, end_var, s, e):
    # intervals are [start,end), [s,e) -> no overlap if end <= s or start >= e
    return Or(end_var <= s, start_var >= e)

# Apply non-overlap constraints per day for both participants
for d in [MON, TUE, WED]:
    for (s, e) in stephanie_busy[d]:
        opt.add(Implies(day == d, no_overlap(start, end, s, e)))
    for (s, e) in betty_busy[d]:
        opt.add(Implies(day == d, no_overlap(start, end, s, e)))

# Preference: avoid Monday (soft)
opt.add_soft(day != MON, weight="1")

# Constraint: On Tuesday, meeting must finish by 12:30
opt.add(Implies(day == TUE, end <= to_min(12, 30)))

# Prefer earlier times
opt.minimize(start)

# Solve
if opt.check() == sat:
    m = opt.model()
    d = m[day].as_long()
    s = m[start].as_long()
    e = m[end].as_long()

    def fmt(t):
        hh = 9 + (t // 60)
        mm = t % 60
        return f"{hh:02d}:{mm:02d}"

    print(day_names[d])
    print(f"{{{fmt(s)}:{fmt(e)}}}")
else:
    print("No solution found.")