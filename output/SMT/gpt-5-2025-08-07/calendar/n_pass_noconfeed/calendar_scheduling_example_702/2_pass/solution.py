from z3 import Optimize, Int, And, Or, Implies, BoolVal, sat

# Problem data
days = ["Monday", "Tuesday", "Wednesday"]
day_index = {d: i for i, d in enumerate(days)}
work_start = 9 * 60  # 09:00 in minutes
work_end = 17 * 60   # 17:00 in minutes
duration = 30        # 30 minutes
slots_per_day = (work_end - work_start) // duration  # 16 half-hour slots

def to_min(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

# Busy schedules per participant per day
busy = {
    "Robert": {
        "Monday":    [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
        "Tuesday":   [("10:30", "11:00"), ("15:00", "15:30")],
        "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                      ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
    },
    "Ralph": {
        "Monday":    [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
        "Tuesday":   [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "11:30"),
                      ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"),
                      ("16:30", "17:00")],
    }
}

# Convert busy strings to minute ranges
busy_min = {}
for person, days_busy in busy.items():
    busy_min[person] = {}
    for d, intervals in days_busy.items():
        busy_min[person][d] = [(to_min(s), to_min(e)) for (s, e) in intervals]

# Z3 model
opt = Optimize()

day = Int("day")     # 0=Monday, 1=Tuesday, 2=Wednesday
slot = Int("slot")   # 0..15; start time = 09:00 + 30*slot (minutes)

opt.add(day >= 0, day <= 2)
opt.add(slot >= 0, slot < slots_per_day)

start_min = work_start + slot * duration
end_min = start_min + duration

# Within work hours
opt.add(start_min >= work_start, end_min <= work_end)

# No overlap with each participant's busy times on the chosen day
for di, dname in enumerate(days):
    per_day_constraints = []
    for person in busy_min:
        constraints = []
        for (bs, be) in busy_min[person][dname]:
            constraints.append(Or(end_min <= bs, start_min >= be))
        per_person_free = And(constraints) if constraints else BoolVal(True)
        per_day_constraints.append(per_person_free)
    opt.add(Implies(day == di, And(per_day_constraints)))

# Preference: avoid Monday if possible (soft constraint)
opt.add_soft(day != day_index["Monday"], weight=1, id="avoid_monday")

# Objective: earliest feasible time (day earlier in week, then earlier time)
abs_min_from_week_start = day * 1440 + start_min
opt.minimize(abs_min_from_week_start)

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found, but one was expected per problem statement.")

model = opt.model()
d_val = model[day].as_long()
s_val = model[slot].as_long()

start = work_start + s_val * duration
end = start + duration

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

day_name = days[d_val]
start_str = fmt(start)
end_str = fmt(end)

# Output: day on one line, and the time range in {HH:MM:HH:MM} on another line
print(day_name)
print(f"{{{start_str}:{end_str}}}")