from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Create solver
s = Solver()

# Variables
start = Int('start')   # meeting start time in minutes from 00:00
end = Int('end')       # meeting end time in minutes from 00:00
day = Int('day')       # 0=Monday, ..., 6=Sunday

# Constants
DURATION = 60
WORK_START = minutes(9, 0)   # 09:00
WORK_END = minutes(17, 0)    # 17:00

# Meeting duration
s.add(end == start + DURATION)

# Day constraint: Monday
s.add(day == 0)

# Work hours constraint (meeting entirely within work hours)
s.add(start >= WORK_START, end <= WORK_END)

# Busy schedules (half-open intervals [start, end))
# Anthony: 9:30-10:00, 12:00-13:00, 16:00-16:30
anthony_busy = [
    (minutes(9,30), minutes(10,0)),
    (minutes(12,0), minutes(13,0)),
    (minutes(16,0), minutes(16,30)),
]

# Pamela: 9:30-10:00, 16:30-17:00
pamela_busy = [
    (minutes(9,30), minutes(10,0)),
    (minutes(16,30), minutes(17,0)),
]

# Zachary: 9:00-11:30, 12:00-12:30, 13:00-13:30, 14:30-15:00, 16:00-17:00
zachary_busy = [
    (minutes(9,0), minutes(11,30)),
    (minutes(12,0), minutes(12,30)),
    (minutes(13,0), minutes(13,30)),
    (minutes(14,30), minutes(15,0)),
    (minutes(16,0), minutes(17,0)),
]

def no_overlap_constraints(start_var, end_var, intervals):
    cons = []
    for a, b in intervals:
        cons.append(Or(end_var <= a, start_var >= b))
    return cons

# Add no-overlap constraints for each participant
s.add(no_overlap_constraints(start, end, anthony_busy))
s.add(no_overlap_constraints(start, end, pamela_busy))
s.add(no_overlap_constraints(start, end, zachary_busy))

# Pamela prefers not to meet after 14:30 (meeting must end by 14:30)
s.add(end <= minutes(14,30))

# Solve
if s.check() == sat:
    m = s.model()
    start_min = m[start].as_long()
    end_min = m[end].as_long()
    day_val = m[day].as_long()

    day_names = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
    day_name = day_names[day_val]

    start_str = fmt_time(start_min)
    end_str = fmt_time(end_min)

    print(day_name)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No feasible meeting time found.")