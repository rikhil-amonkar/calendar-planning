from z3 import Int, Solver, And, Or, If, sat

# Helper functions
def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Days mapping
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
day_to_idx = {d: i for i, d in enumerate(days)}

# Busy schedules
schedules = {
    "Laura": {
        "Monday":    [("10:30", "11:00"), ("12:30", "13:00"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Tuesday":   [("09:30", "10:00"), ("11:00", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "17:00")],
        "Wednesday": [("11:30", "12:00"), ("12:30", "13:00"), ("15:30", "16:30")],
        "Thursday":  [("10:30", "11:00"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    },
    "Philip": {
        "Monday":    [("09:00", "17:00")],
        "Tuesday":   [("09:00", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "16:30")],
        "Wednesday": [("09:00", "10:00"), ("11:00", "12:00"), ("12:30", "16:00"), ("16:30", "17:00")],
        "Thursday":  [("09:00", "10:30"), ("11:00", "12:30"), ("13:00", "17:00")],
    }
}

# Convert schedules to minutes
sched_min = {}
for person, per_days in schedules.items():
    sched_min[person] = {}
    for d, intervals in per_days.items():
        sched_min[person][d] = [(to_minutes(s), to_minutes(e)) for (s, e) in intervals]

# Z3 variables
day = Int("day")       # 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
start = Int("start")   # minutes from 00:00
duration = 60
end = start + duration

s = Solver()

# Working hours constraint: between 09:00 and 17:00
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
s.add(start >= work_start, end <= work_end)

# Day domain: Monday..Thursday
s.add(And(day >= 0, day <= 3))

# Extra constraint: Philip cannot meet on Wednesday
s.add(day != day_to_idx["Wednesday"])

# No-overlap constraints for each participant on the chosen day
def no_overlap_for(person):
    constraints = []
    for i, dname in enumerate(days):
        intervals = sched_min[person][dname]
        # For the selected day, the meeting must not overlap any busy interval
        day_constraints = []
        for (bs, be) in intervals:
            # Meeting [start, end) does not overlap [bs, be)
            day_constraints.append(Or(end <= bs, start >= be))
        # If this day is chosen, all its no-overlap constraints must hold
        constraints.append(If(day == i, And(day_constraints) if day_constraints else True, True))
    return And(constraints)

s.add(no_overlap_for("Laura"))
s.add(no_overlap_for("Philip"))

# Solve
if s.check() == sat:
    m = s.model()
    d_idx = m[day].as_long()
    st = m[start].as_long()
    en = st + duration
    print("SOLUTION:")
    print(f"Day: {days[d_idx]}")
    print(f"Start Time: {fmt(st)}")
    print(f"End Time: {fmt(en)}")
else:
    print("No solution found.")