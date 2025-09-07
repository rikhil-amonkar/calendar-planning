from z3 import *

def to_minutes(h, m):
    return h*60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
day = "Monday"
work_start = to_minutes(9, 0)
work_end   = to_minutes(17, 0)
duration   = 30  # minutes

# Busy intervals per participant as (start_min, end_min), half-open [start, end)
busy = {
    "Megan": [
        (to_minutes(9, 0),  to_minutes(9, 30)),
        (to_minutes(10, 0), to_minutes(11, 0)),
        (to_minutes(12, 0), to_minutes(12, 30)),
    ],
    "Christine": [
        (to_minutes(9, 0),  to_minutes(9, 30)),
        (to_minutes(11, 30), to_minutes(12, 0)),
        (to_minutes(13, 0), to_minutes(14, 0)),
        (to_minutes(15, 30), to_minutes(16, 30)),
    ],
    "Gabriel": [
        # Free all day -> no busy intervals
    ],
    "Sara": [
        (to_minutes(11, 30), to_minutes(12, 0)),
        (to_minutes(14, 30), to_minutes(15, 0)),
    ],
    "Bruce": [
        (to_minutes(9, 30),  to_minutes(10, 0)),
        (to_minutes(10, 30), to_minutes(12, 0)),
        (to_minutes(12, 30), to_minutes(14, 0)),
        (to_minutes(14, 30), to_minutes(15, 0)),
        (to_minutes(15, 30), to_minutes(16, 30)),
    ],
    "Kathryn": [
        (to_minutes(10, 0), to_minutes(15, 30)),
        (to_minutes(16, 0), to_minutes(16, 30)),
    ],
    "Billy": [
        (to_minutes(9, 0),  to_minutes(9, 30)),
        (to_minutes(11, 0), to_minutes(11, 30)),
        (to_minutes(12, 0), to_minutes(14, 0)),
        (to_minutes(14, 30), to_minutes(15, 30)),
    ],
}

# Z3 model
s = Optimize()
start = Int("start")
end = Int("end")

# Core constraints
s.add(start >= work_start)
s.add(end == start + duration)
s.add(end <= work_end)
# Align to 30-minute slots
s.add(start % 30 == 0)

# No overlap with any participant's busy intervals
for person, intervals in busy.items():
    for (b_start, b_end) in intervals:
        # meeting [start, end) must be completely before busy or after busy
        s.add(Or(end <= b_start, start >= b_end))

# Prefer earliest feasible time
s.minimize(start)

if s.check() == sat:
    m = s.model()
    st = m[start].as_long()
    en = m[end].as_long()
    time_range = f"{fmt_time(st)}:{fmt_time(en)}"
    print(f"{day} {{{time_range}}}")
else:
    print("No feasible time found")