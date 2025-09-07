from z3 import Solver, Int, Or, And, sat

# Helper to convert HH:MM to minutes since midnight
def to_min(h, m):
    return h * 60 + m

# Helper to format minutes since midnight back to HH:MM
def fmt(m):
    return f"{m//60:02d}:{m%60:02d}"

# Meeting details
day = "Monday"
duration = 60  # minutes
work_start = to_min(9, 0)
work_end = to_min(17, 0)

# Blocked times for each participant on Monday, as [start, end) in minutes since midnight
blocked = {
    "Olivia": [
        (to_min(12, 30), to_min(13, 30)),
        (to_min(14, 30), to_min(15, 0)),
        (to_min(16, 30), to_min(17, 0)),
    ],
    "Anna": [
        # No blocks
    ],
    "Virginia": [
        (to_min(9, 0), to_min(10, 0)),
        (to_min(11, 30), to_min(16, 0)),
        (to_min(16, 30), to_min(17, 0)),
    ],
    "Paul": [
        (to_min(9, 0), to_min(9, 30)),
        (to_min(11, 0), to_min(11, 30)),
        (to_min(13, 0), to_min(14, 0)),
        (to_min(14, 30), to_min(16, 0)),
        (to_min(16, 30), to_min(17, 0)),
    ],
}

# Z3 variables
start = Int("start")
end = Int("end")

s = Solver()

# Duration and work hours constraints
s.add(end == start + duration)
s.add(start >= work_start)
s.add(end <= work_end)

# No-overlap constraints with each participant's blocked intervals
for person, intervals in blocked.items():
    for (bs, be) in intervals:
        # Meeting [start, end) does not overlap blocked [bs, be)
        s.add(Or(end <= bs, start >= be))

# Solve
if s.check() == sat:
    model = s.model()
    st = model[start].as_long()
    en = model[end].as_long()
    print(f"{day} {{{fmt(st)}:{fmt(en)}}}")
else:
    print("No feasible meeting time found.")