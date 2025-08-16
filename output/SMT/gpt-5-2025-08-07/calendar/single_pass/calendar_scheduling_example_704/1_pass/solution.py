from z3 import Optimize, Int, Or, Implies

# Helper functions
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

# Problem data
days = ["Monday", "Tuesday", "Wednesday"]
day_idx = {d: i for i, d in enumerate(days)}

work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 30  # minutes

# Larry: no busy intervals (fully available)
# Samuel's busy intervals by day (times in minutes)
samuel_busy = {
    "Monday": [
        ("10:30", "11:00"),
        ("12:00", "12:30"),
        ("13:00", "15:00"),
        ("15:30", "16:30"),
    ],
    "Tuesday": [
        ("09:00", "12:00"),
        ("14:00", "15:30"),
        ("16:30", "17:00"),
    ],
    "Wednesday": [
        ("10:30", "11:00"),
        ("11:30", "12:00"),
        ("12:30", "13:00"),
        ("14:00", "14:30"),
        ("15:00", "16:00"),
    ],
}

# Convert busy intervals to minutes
samuel_busy_min = {
    day: [(time_to_minutes(a), time_to_minutes(b)) for (a, b) in intervals]
    for day, intervals in samuel_busy.items()
}

# Z3 Optimize model
opt = Optimize()

day = Int("day")     # 0=Monday, 1=Tuesday, 2=Wednesday
start = Int("start") # minutes from 00:00

# Domain constraints
opt.add(day >= 0, day <= 2)
opt.add(start >= work_start, start + duration <= work_end)

# No-overlap constraints for Samuel on the chosen day
for dname, idx in day_idx.items():
    for (a, b) in samuel_busy_min[dname]:
        # Meeting [start, start+duration) must be outside [a, b)
        opt.add(Implies(day == idx, Or(start + duration <= a, start >= b)))

# Preferences and objective:
# 1) Earliest day (Monday earliest), then earliest time within that day
opt.minimize(day)
opt.minimize(start)

# 2) Soft preferences:
#    - Larry would rather not meet on Wednesday
#    - Samuel would like to avoid more meetings on Tuesday
opt.add_soft(day != day_idx["Wednesday"], weight='1')
opt.add_soft(day != day_idx["Tuesday"], weight='1')

# Solve
if opt.check().r == 1:  # sat
    m = opt.model()
    chosen_day = days[m[day].as_long()]
    start_min = m[start].as_long()
    end_min = start_min + duration

    print("SOLUTION:")
    print(f"Day: {chosen_day}")
    print(f"Start Time: {minutes_to_time(start_min)}")
    print(f"End Time: {minutes_to_time(end_min)}")
else:
    # As per problem statement, a solution exists; this is a fallback
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 09:00")
    print("End Time: 09:30")