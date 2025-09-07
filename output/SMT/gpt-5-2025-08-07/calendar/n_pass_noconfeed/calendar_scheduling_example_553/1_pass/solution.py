# Meeting Scheduler using Z3 SMT Solver
# Task: Schedule a 30-minute meeting for Eric and Henry on Monday between 09:00 and 17:00,
# respecting their existing busy times and Henry's preference to not meet after 10:00.

import sys
import subprocess

# Ensure z3-solver is available
try:
    from z3 import Optimize, Int, Or, And
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "z3-solver"])
    from z3 import Optimize, Int, Or, And

def minutes(hh, mm):
    return hh * 60 + mm

def fmt_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Work hours and meeting duration
DAY = "Monday"
WORK_START = minutes(9, 0)   # 09:00
WORK_END   = minutes(17, 0)  # 17:00
DURATION = 30                # 30 minutes

# Busy schedules (start, end) in minutes since 00:00
# Eric: 12:00-13:00, 14:00-15:00
eric_busy = [
    (minutes(12, 0), minutes(13, 0)),
    (minutes(14, 0), minutes(15, 0)),
]

# Henry: 09:30-10:00, 10:30-11:00, 11:30-12:30, 13:00-13:30, 14:30-15:00, 16:00-17:00
henry_busy = [
    (minutes(9, 30), minutes(10, 0)),
    (minutes(10, 30), minutes(11, 0)),
    (minutes(11, 30), minutes(12, 30)),
    (minutes(13, 0), minutes(13, 30)),
    (minutes(14, 30), minutes(15, 0)),
    (minutes(16, 0), minutes(17, 0)),
]

# Z3 model
opt = Optimize()
start = Int("start")
end = Int("end")

# Core constraints
opt.add(
    And(
        start >= WORK_START,
        end == start + DURATION,
        end <= WORK_END
    )
)

# Non-overlap constraints with Eric's busy times
for (bs, be) in eric_busy:
    opt.add(Or(end <= bs, start >= be))

# Non-overlap constraints with Henry's busy times
for (bs, be) in henry_busy:
    opt.add(Or(end <= bs, start >= be))

# Preference: Henry would rather not meet after 10:00 (i.e., prefer start <= 10:00)
PREF_LATEST_START = minutes(10, 0)
opt.add_soft(start <= PREF_LATEST_START, weight="1")

# Tie-breaker: choose the earliest feasible start time
opt.minimize(start)

if opt.check().r == 1:  # sat
    model = opt.model()
    s = model[start].as_long()
    e = s + DURATION
    print(DAY)
    print(f"{{{fmt_time(s)}:{fmt_time(e)}}}")
else:
    print("No feasible meeting time found.")