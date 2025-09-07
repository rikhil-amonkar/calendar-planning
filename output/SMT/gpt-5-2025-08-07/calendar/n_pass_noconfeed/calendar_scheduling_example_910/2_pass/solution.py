from z3 import *

# Meeting parameters
duration = 60  # minutes
work_start = 0         # 9:00 mapped to 0 minutes
work_end = 8 * 60      # 17:00 mapped to 480 minutes

# Days mapping
days = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Helper to convert HH:MM to minutes from 9:00
def t(hh, mm):
    return (hh - 9) * 60 + mm

# Busy schedules as (day_index, start_min, end_min) relative to 9:00
# Bryan's schedule
bryan_busy = [
    (3, t(9, 30),  t(10, 0)),   # Thursday 09:30-10:00
    (3, t(12, 30), t(13, 0)),   # Thursday 12:30-13:00
    (4, t(10, 30), t(11, 0)),   # Friday   10:30-11:00
    (4, t(14, 0),  t(14, 30)),  # Friday   14:00-14:30
]

# Nicholas's schedule
nicholas_busy = [
    # Monday
    (0, t(11, 30), t(12, 0)),
    (0, t(13, 0),  t(15, 30)),
    # Tuesday
    (1, t(9, 0),   t(9, 30)),
    (1, t(11, 0),  t(13, 30)),
    (1, t(14, 0),  t(16, 30)),
    # Wednesday
    (2, t(9, 0),   t(9, 30)),
    (2, t(10, 0),  t(11, 0)),
    (2, t(11, 30), t(13, 30)),
    (2, t(14, 0),  t(14, 30)),
    (2, t(15, 0),  t(16, 30)),
    # Thursday
    (3, t(10, 30), t(11, 30)),
    (3, t(12, 0),  t(12, 30)),
    (3, t(15, 0),  t(15, 30)),
    (3, t(16, 30), t(17, 0)),
    # Friday
    (4, t(9, 0),   t(10, 30)),
    (4, t(11, 0),  t(12, 0)),
    (4, t(12, 30), t(14, 30)),
    (4, t(15, 30), t(16, 0)),
    (4, t(16, 30), t(17, 0)),
]

# Z3 variables
day = Int('day')     # 0=Mon ... 4=Fri
start = Int('start') # minutes from 9:00 within the chosen day
end = Int('end')

opt = Optimize()

# Basic bounds
opt.add(day >= 0, day <= 4)
opt.add(start >= work_start, start <= work_end - duration)
opt.add(end == start + duration)

# Use 30-minute granularity without Mod
k30 = Int('k30')
opt.add(k30 >= 0)
opt.add(start == 30 * k30)

# Non-overlap constraints helper
def add_no_overlap(busy_list):
    for d, s, e in busy_list:
        # If meeting is on day d, it must not overlap [s, e)
        opt.add(Implies(day == d, Or(end <= s, start >= e)))

# Apply non-overlap for both participants
add_no_overlap(bryan_busy)
add_no_overlap(nicholas_busy)

# Preferences (soft constraints as penalties)
# Bryan would like to avoid Tuesday (day == 1)
p_bryan_tue = If(day == 1, 1, 0)
# Nicholas would rather not meet on Monday and Thursday (days 0 and 3)
p_nich_mon = If(day == 0, 1, 0)
p_nich_thu = If(day == 3, 1, 0)

total_penalty = Int('total_penalty')
opt.add(total_penalty == p_bryan_tue + p_nich_mon + p_nich_thu)

# Optimize: minimize violations first, then choose earliest time
opt.minimize(total_penalty)
opt.minimize(start)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible meeting time found.")

m = opt.model()
chosen_day = m[day].as_long()
s = m[start].as_long()
e = m[end].as_long()

def fmt(mins):
    hh = 9 + mins // 60
    mm = mins % 60
    return f"{hh:02d}:{mm:02d}"

# Output day and time in required format
print(days[chosen_day])
print(f"{{{fmt(s)}:{fmt(e)}}}")