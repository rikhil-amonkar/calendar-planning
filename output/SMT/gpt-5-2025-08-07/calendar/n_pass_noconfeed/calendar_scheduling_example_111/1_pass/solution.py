from z3 import *

def to_min(h, m):
    return h * 60 + m

def hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Problem setup
day = "Monday"
work_start = to_min(9, 0)
work_end = to_min(17, 0)
duration = 30  # minutes

# Blocked intervals [start, end) in minutes from 00:00
Gregory = [
    (to_min(9, 0), to_min(10, 0)),
    (to_min(10, 30), to_min(11, 30)),
    (to_min(12, 30), to_min(13, 0)),
    (to_min(13, 30), to_min(14, 0)),
]

Natalie = []  # wide open

Christine = [
    (to_min(9, 0), to_min(11, 30)),
    (to_min(13, 30), to_min(17, 0)),
]

Vincent = [
    (to_min(9, 0), to_min(9, 30)),
    (to_min(10, 30), to_min(12, 0)),
    (to_min(12, 30), to_min(14, 0)),
    (to_min(14, 30), to_min(17, 0)),
]

participants = {
    "Gregory": Gregory,
    "Natalie": Natalie,
    "Christine": Christine,
    "Vincent": Vincent,
}

# Z3 model
opt = Optimize()
start = Int("start")
end = Int("end")

# Core constraints
opt.add(start >= work_start)
opt.add(end == start + duration)
opt.add(end <= work_end)

# Optional: align on 30-minute boundaries
opt.add(start % 30 == 0)

# Availability constraints (no overlap with any blocked interval)
def no_overlap_with(intervals):
    cons = []
    for a, b in intervals:
        cons.append(Or(end <= a, start >= b))
    return And(cons) if cons else True

for name, blocks in participants.items():
    opt.add(no_overlap_with(blocks))

# Prefer earliest feasible time
opt.minimize(start)

if opt.check() == sat:
    m = opt.model()
    s = m[start].as_long()
    e = m[end].as_long()
    print(f"{day} {{{hhmm(s)}:{hhmm(e)}}}")
else:
    print("No solution found")