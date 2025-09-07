from z3 import *

# Meeting setup
DAY = "Monday"
WORK_START = 9 * 60      # 09:00 in minutes from midnight
WORK_END = 17 * 60       # 17:00 in minutes from midnight
DURATION = 30            # 30 minutes

# Represent time as minutes from 09:00 to simplify constraints
DAY_START = 0
DAY_END = (WORK_END - WORK_START)  # 480 minutes (8 hours)

# Busy intervals for each participant as [start, end) in minutes from 09:00
Jacqueline_busy = [
    (0, 30),    # 09:00-09:30
    (120, 150), # 11:00-11:30
    (210, 240), # 12:30-13:00
    (390, 420), # 15:30-16:00
]

Harold_busy = [
    (60, 90),   # 10:00-10:30
    (240, 270), # 13:00-13:30
    (360, 480), # 15:00-17:00
]

Arthur_busy = [
    (0, 30),    # 09:00-09:30
    (60, 210),  # 10:00-12:30
    (330, 360), # 14:30-15:00
    (390, 480), # 15:30-17:00
]

Kelly_busy = [
    (0, 30),    # 09:00-09:30
    (60, 120),  # 10:00-11:00
    (150, 210), # 11:30-12:30
    (300, 360), # 14:00-15:00
    (390, 420), # 15:30-16:00
]

def no_overlap_constraints(start, end, busy_list):
    """Generate Z3 constraints ensuring [start, end) does not overlap any busy interval."""
    cons = []
    for b_start, b_end in busy_list:
        cons.append(Or(end <= b_start, start >= b_end))
    return cons

# Variables
start = Int('start')
end = Int('end')

opt = Optimize()

# Core constraints
opt.add(start >= DAY_START)
opt.add(end == start + DURATION)
opt.add(end <= DAY_END)

# Align meeting start to 30-minute increments
opt.add(start % 30 == 0)

# Participants' availability
opt.add(no_overlap_constraints(start, end, Jacqueline_busy))
opt.add(no_overlap_constraints(start, end, Harold_busy))
opt.add(no_overlap_constraints(start, end, Arthur_busy))
opt.add(no_overlap_constraints(start, end, Kelly_busy))

# Preference: Harold does not want to meet after 13:00 on Monday (i.e., meeting must end by 13:00)
# 13:00 is 4 hours after 09:00 -> 240 minutes from DAY_START
opt.add(end <= 240)

# Optional: choose the earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    s = m[start].as_long()
    e = m[end].as_long()

    # Convert from minutes-from-09:00 to HH:MM
    def to_hhmm(offset_from_day_start):
        total_minutes = WORK_START + offset_from_day_start
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    start_str = to_hhmm(s)
    end_str = to_hhmm(e)

    print(DAY)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No feasible time found.")