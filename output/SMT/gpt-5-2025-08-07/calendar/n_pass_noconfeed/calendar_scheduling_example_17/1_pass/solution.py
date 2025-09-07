# Z3-based meeting scheduler for Margaret, Donna, and Helen
# Task: Find a 30-minute meeting on Monday between 09:00 and 17:00
# respecting each participant's blocked times and Helen's preference
# not to meet after 13:30.

from z3 import Int, Or, And, Solver, sat

def to_minutes(hh, mm):
    return hh * 60 + mm

def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Workday bounds for Monday
work_start = to_minutes(9, 0)    # 09:00
work_end   = to_minutes(17, 0)   # 17:00
duration   = 30                  # 30 minutes

# Participants' blocked intervals on Monday: [start, end) in minutes
margaret_busy = [
    (to_minutes(9, 0),  to_minutes(10, 0)),
    (to_minutes(10, 30), to_minutes(11, 0)),
    (to_minutes(11, 30), to_minutes(12, 0)),
    (to_minutes(13, 0),  to_minutes(13, 30)),
    (to_minutes(15, 0),  to_minutes(15, 30)),
]

donna_busy = [
    (to_minutes(14, 30), to_minutes(15, 0)),
    (to_minutes(16, 0),  to_minutes(16, 30)),
]

helen_busy = [
    (to_minutes(9, 0),   to_minutes(9, 30)),
    (to_minutes(10, 0),  to_minutes(11, 30)),
    (to_minutes(13, 0),  to_minutes(14, 0)),
    (to_minutes(14, 30), to_minutes(15, 0)),
    (to_minutes(15, 30), to_minutes(17, 0)),
]

# Preference: Helen does not want to meet after 13:30
helen_latest_end = to_minutes(13, 30)

# Z3 variables
start = Int("start")
end   = Int("end")

s = Solver()

# Basic meeting constraints
s.add(start >= work_start)
s.add(end == start + duration)
s.add(end <= work_end)

# Apply Helen's "not after 13:30" preference (no portion after 13:30)
s.add(end <= helen_latest_end)

# No overlap with any participant's blocked times
def no_overlap_with(intervals):
    constraints = []
    for (b_start, b_end) in intervals:
        # Meeting entirely before the busy interval OR entirely after
        constraints.append(Or(end <= b_start, start >= b_end))
    return And(constraints) if constraints else True

s.add(no_overlap_with(margaret_busy))
s.add(no_overlap_with(donna_busy))
s.add(no_overlap_with(helen_busy))

if s.check() == sat:
    m = s.model()
    st = m[start].as_long()
    en = m[end].as_long()
    # Output includes both the day of the week and the time range in HH:MM:HH:MM format
    print(f"Monday {{{fmt(st)}:{fmt(en)}}}")
else:
    print("No feasible meeting time found.")