from z3 import *

def to_minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
duration = 30  # minutes
work_start = to_minutes(9, 0)
work_end = to_minutes(17, 0)

# Busy intervals (start, end) in minutes since 00:00
Judy_busy = [
    (to_minutes(13, 0), to_minutes(13, 30)),
    (to_minutes(16, 0), to_minutes(16, 30)),
]
Olivia_busy = [
    (to_minutes(10, 0), to_minutes(10, 30)),
    (to_minutes(12, 0), to_minutes(13, 0)),
    (to_minutes(14, 0), to_minutes(14, 30)),
]
Eric_busy = []  # free entire day
Jacqueline_busy = [
    (to_minutes(10, 0), to_minutes(10, 30)),
    (to_minutes(15, 0), to_minutes(15, 30)),
]
Laura_busy = [
    (to_minutes(9, 0), to_minutes(10, 0)),
    (to_minutes(10, 30), to_minutes(12, 0)),
    (to_minutes(13, 0), to_minutes(13, 30)),
    (to_minutes(14, 30), to_minutes(15, 0)),
    (to_minutes(15, 30), to_minutes(17, 0)),
]
Tyler_busy = [
    (to_minutes(9, 0), to_minutes(10, 0)),
    (to_minutes(11, 0), to_minutes(11, 30)),
    (to_minutes(12, 30), to_minutes(13, 0)),
    (to_minutes(14, 0), to_minutes(14, 30)),
    (to_minutes(15, 30), to_minutes(17, 0)),
]
Lisa_busy = [
    (to_minutes(9, 30), to_minutes(10, 30)),
    (to_minutes(11, 0), to_minutes(11, 30)),
    (to_minutes(12, 0), to_minutes(12, 30)),
    (to_minutes(13, 0), to_minutes(13, 30)),
    (to_minutes(14, 0), to_minutes(14, 30)),
    (to_minutes(16, 0), to_minutes(17, 0)),
]

participants_busy = [
    Judy_busy, Olivia_busy, Eric_busy, Jacqueline_busy,
    Laura_busy, Tyler_busy, Lisa_busy
]

# Z3 variables
start = Int('start')
end = Int('end')

o = Optimize()

# Basic constraints
o.add(end == start + duration)
o.add(start >= work_start, end <= work_end)
# Force 30-minute grid
o.add(start % 30 == 0)

# Non-overlap constraint helper
def no_overlap(s, e, bs, be):
    # Meeting [s, e) does not overlap busy [bs, be)
    return Or(e <= bs, s >= be)

# Add constraints for each participant's busy times
for busy_list in participants_busy:
    for (bs, be) in busy_list:
        o.add(no_overlap(start, end, bs, be))

# Prefer earliest feasible start
o.minimize(start)

if o.check() == sat:
    m = o.model()
    s = m[start].as_long()
    e = m[end].as_long()
    print("Monday")
    print("{" + f"{fmt_time(s)}:{fmt_time(e)}" + "}")
else:
    # Fallback (should not happen as per problem statement)
    print("Monday")
    print("{No Solution}")