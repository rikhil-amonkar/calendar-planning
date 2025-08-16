# Requires: z3-solver (pip install z3-solver)
from z3 import Int, Optimize, And, Or, Implies, sat

# Helper functions
def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def from_minutes(m):
    h = m // 60
    mins = m % 60
    return f"{h:02d}:{mins:02d}"

# Problem data
days = ["Monday", "Tuesday", "Wednesday"]
day_index = {d: i for i, d in enumerate(days)}

work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 60  # minutes

# Participants' busy schedules (per day)
# Patrick: free all week (no busy intervals)
# Roy's busy slots as given
roy_busy = {
    "Monday":    [("10:00","11:30"), ("12:00","13:00"), ("14:00","14:30"), ("15:00","17:00")],
    "Tuesday":   [("10:30","11:30"), ("12:00","14:30"), ("15:00","15:30"), ("16:00","17:00")],
    "Wednesday": [("09:30","11:30"), ("12:30","14:00"), ("14:30","15:30"), ("16:30","17:00")],
}

# Aggregate busy intervals for all participants per day
busy_by_day = {i: [] for i in range(len(days))}
for d in days:
    i = day_index[d]
    # Patrick has no busy intervals
    for s, e in roy_busy.get(d, []):
        busy_by_day[i].append((to_minutes(s), to_minutes(e)))

# Z3 variables
day = Int("day")       # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start = Int("start")   # minutes from midnight

opt = Optimize()
opt.add(And(day >= 0, day < len(days)))

# Enforce feasibility per selected day
for i in range(len(days)):
    constraints = []
    # Meeting within work hours
    constraints.append(And(start >= work_start, start + meeting_duration <= work_end))
    # No overlap with any busy interval on that day
    for (bs, be) in busy_by_day[i]:
        constraints.append(Or(start + meeting_duration <= bs, start >= be))
    opt.add(Implies(day == i, And(constraints)))

# Earliest availability: minimize day first, then start time
opt.minimize(day)
opt.minimize(start)

if opt.check() != sat:
    raise RuntimeError("No feasible schedule found, but the problem statement guaranteed a solution.")

m = opt.model()
chosen_day_idx = m[day].as_long()
chosen_start = m[start].as_long()
chosen_end = chosen_start + meeting_duration

print("SOLUTION:")
print(f"Day: {days[chosen_day_idx]}")
print(f"Start Time: {from_minutes(chosen_start)} (24-hour format)")
print(f"End Time: {from_minutes(chosen_end)} (24-hour format)")