from z3 import *

# Helper to convert HH:MM to minutes since midnight
def to_minutes(h, m):
    return h * 60 + m

# Helper to format minutes since midnight to HH:MM
def fmt(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Problem setup
work_start = to_minutes(9, 0)   # 09:00
work_end   = to_minutes(17, 0)  # 17:00
duration   = 30                 # 30 minutes

# Day indices: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
day_names = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Existing schedules (busy intervals are half-open [start, end))
# Julie: no busy intervals
julie_busy = {
    0: [],
    1: [],
    2: [],
    3: []
}

# Ruth's busy schedule
ruth_busy = {
    0: [(to_minutes(9, 0), to_minutes(17, 0))],  # Monday: 09:00-17:00
    1: [(to_minutes(9, 0), to_minutes(17, 0))],  # Tuesday: 09:00-17:00
    2: [(to_minutes(9, 0), to_minutes(17, 0))],  # Wednesday: 09:00-17:00
    3: [  # Thursday
        (to_minutes(9, 0),  to_minutes(11, 0)),
        (to_minutes(11, 30), to_minutes(14, 30)),
        (to_minutes(15, 0), to_minutes(17, 0)),
    ]
}

opt = Optimize()

# Variables
day   = Int("day")
start = Int("start")
end   = Int("end")

# Basic constraints
opt.add(day >= 0, day <= 3)
opt.add(end == start + duration)
opt.add(work_start <= start, end <= work_end)
# Start on 30-minute boundaries for clean times
opt.add(start % 30 == 0)

# Non-overlap with busy intervals for each participant, conditioned on chosen day
def add_non_overlap_for_person(busy_map):
    for d in range(4):
        clauses = []
        for (s, e) in busy_map[d]:
            # Meeting [start, end) must not intersect [s, e)
            clauses.append(Or(end <= s, start >= e))
        # If there are no busy intervals that day, it's trivially true
        if clauses:
            opt.add(Implies(day == d, And(clauses)))
        else:
            opt.add(Implies(day == d, True))

add_non_overlap_for_person(julie_busy)
add_non_overlap_for_person(ruth_busy)

# Preference: Julie would like to avoid meetings on Thursday before 11:30
# Soft constraint: if day == Thursday (3), prefer start >= 11:30 (690)
opt.add_soft(Or(day != 3, start >= to_minutes(11, 30)), weight="1", id="prefer_thu_after_1130")

# Solve
if opt.check() == sat:
    model = opt.model()
    d = model.eval(day).as_long()
    s = model.eval(start).as_long()
    e = s + duration
    print(f"{day_names[d]} {{{fmt(s)}:{fmt(e)}}}")
else:
    print("No solution found.")