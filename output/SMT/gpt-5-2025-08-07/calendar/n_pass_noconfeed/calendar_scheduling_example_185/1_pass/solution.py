from z3 import Optimize, Int, Or, sat

# Helper to convert minutes to HH:MM
def minutes_to_hhmm(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Time helper
def t(h, m):
    return h * 60 + m

# Meeting parameters
DAY = "Monday"
WORK_START = t(9, 0)
WORK_END = t(17, 0)
DURATION = 30  # minutes

# Busy schedules (Monday)
kimberly_busy = [
    (t(10, 0), t(10, 30)),
    (t(11, 0), t(12, 0)),
    (t(16, 0), t(16, 30)),
]

megan_busy = [
    # No meetings
]

marie_busy = [
    (t(10, 0), t(11, 0)),
    (t(11, 30), t(15, 0)),
    (t(16, 0), t(16, 30)),
]

diana_busy = [
    (t(9, 30), t(10, 0)),
    (t(10, 30), t(14, 30)),
    (t(15, 30), t(17, 0)),
]

all_schedules = [
    kimberly_busy,
    megan_busy,
    marie_busy,
    diana_busy,
]

# Z3 model
opt = Optimize()
start = Int("start")
end = Int("end")

# Meeting duration and work hours
opt.add(end == start + DURATION)
opt.add(start >= WORK_START, end <= WORK_END)

# Non-overlap constraints: [start, end) does not intersect with any busy [bs, be)
for sched in all_schedules:
    for (bs, be) in sched:
        opt.add(Or(end <= bs, start >= be))

# Preference: Megan would like to avoid meetings before 10:00
opt.add_soft(start >= t(10, 0), 1, "prefer_after_10")

# Among preferred times, choose the earliest feasible start
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s = model[start].as_long()
    e = model[end].as_long()
    s_str = minutes_to_hhmm(s)
    e_str = minutes_to_hhmm(e)

    # Outputs:
    # 1) HH:MM:HH:MM
    print(f"{s_str}:{e_str}")
    # 2) Day of the week
    print(DAY)
    # 3) Curly-brace time range as requested example format
    print(f"{{{s_str}:{e_str}}}")
else:
    print("No feasible meeting time found.")