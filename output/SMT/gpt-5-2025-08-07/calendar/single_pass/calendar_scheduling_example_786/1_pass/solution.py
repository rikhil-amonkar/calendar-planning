from z3 import Optimize, Int, Or, And, Implies

def minutes(h, m):
    return h * 60 + m

def minute_to_str(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Problem parameters
work_start = minutes(9, 0)     # 09:00
work_end   = minutes(17, 0)    # 17:00
duration   = 30                # 30 minutes
days = ["Monday", "Tuesday", "Wednesday"]
MON, TUE, WED = 0, 1, 2

# Busy schedules: list of (day_index, start_min, end_min) for each participant
busy = {
    "Amy": [
        (WED, minutes(11, 0), minutes(11, 30)),
        (WED, minutes(13, 30), minutes(14, 0)),
    ],
    "Pamela": [
        # Monday
        (MON, minutes(9, 0), minutes(10, 30)),
        (MON, minutes(11, 0), minutes(16, 30)),
        # Tuesday
        (TUE, minutes(9, 0), minutes(9, 30)),
        (TUE, minutes(10, 0), minutes(17, 0)),
        # Wednesday
        (WED, minutes(9, 0), minutes(9, 30)),
        (WED, minutes(10, 0), minutes(11, 0)),
        (WED, minutes(11, 30), minutes(13, 30)),
        (WED, minutes(14, 30), minutes(15, 0)),
        (WED, minutes(16, 0), minutes(16, 30)),
    ],
}

# Z3 model
opt = Optimize()

# Decision variables
d = Int("day")       # 0=Mon,1=Tue,2=Wed
s = Int("start")     # start time in minutes from midnight

# Domain constraints
opt.add(d >= MON, d <= WED)
opt.add(s >= work_start)
opt.add(s + duration <= work_end)

# Start times on 30-minute increments
opt.add(((s - work_start) % 30) == 0)

# No-overlap constraints for each participant's busy times on the selected day
for person, intervals in busy.items():
    for (bd, bstart, bend) in intervals:
        # Meeting [s, s+duration) must not intersect busy [bstart, bend)
        opt.add(Implies(d == bd, Or(s + duration <= bstart, s >= bend)))

# Preferences (soft constraints):
# Pamela would like to avoid Monday, avoid Tuesday, and avoid Wednesday before 16:00
opt.add_soft(d != MON, 1, "avoid_monday")
opt.add_soft(d != TUE, 1, "avoid_tuesday")
opt.add_soft(Or(d != WED, s >= minutes(16, 0)), 1, "wednesday_after_16")

# Solve
if opt.check() != sat:
    raise RuntimeError("No feasible schedule found (unexpected per problem statement).")

m = opt.model()
day_val = m[d].as_long()
start_val = m[s].as_long()
end_val = start_val + duration

# Output in required format
print("SOLUTION:")
print(f"Day: {days[day_val]}")
print(f"Start Time: {minute_to_str(start_val)} (24-hour format)")
print(f"End Time: {minute_to_str(end_val)} (24-hour format)")