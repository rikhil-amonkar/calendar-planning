from z3 import *

def minutes(h, m):
    return h * 60 + m

def fmt(mm):
    h = mm // 60
    m = mm % 60
    return f"{h:02d}:{m:02d}"

# Day of the week
day = "Monday"

# Meeting duration (minutes)
DUR = 30

# Work hours (on Monday): 09:00 to 17:00
WORK_START = minutes(9, 0)
WORK_END   = minutes(17, 0)

# Participants' busy intervals on Monday (half-open [start, end))
christine_busy = [
    (minutes(11, 0), minutes(11, 30)),
    (minutes(15, 0), minutes(15, 30)),
]

helen_busy = [
    (minutes(9, 30),  minutes(10, 30)),
    (minutes(11, 0),  minutes(11, 30)),
    (minutes(12, 0),  minutes(12, 30)),
    (minutes(13, 30), minutes(16, 0)),
    (minutes(16, 30), minutes(17, 0)),
]

# Additional constraint: Helen cannot meet after 15:00 (meeting must end by 15:00)
HELEN_END_DEADLINE = minutes(15, 0)

# Z3 variables
start = Int('start')
end = Int('end')

s = Optimize()

# Basic constraints
s.add(end == start + DUR)
s.add(start >= WORK_START)
s.add(end <= WORK_END)
# Align to 30-minute grid
s.add(Mod(start, 30) == 0)

# Helen's "not after 15:00" constraint
s.add(end <= HELEN_END_DEADLINE)

# No-overlap constraints
def no_overlap(st, en, bstart, bend):
    # Meeting does not intersect [bstart, bend)
    return Or(en <= bstart, st >= bend)

for bstart, bend in christine_busy:
    s.add(no_overlap(start, end, bstart, bend))

for bstart, bend in helen_busy:
    s.add(no_overlap(start, end, bstart, bend))

# Prefer the earliest feasible meeting
s.minimize(start)

if s.check() == sat:
    m = s.model()
    st = m[start].as_long()
    en = m[end].as_long()
    print(day)
    print(f"{{{fmt(st)}:{fmt(en)}}}")
else:
    print("No feasible meeting time found.")