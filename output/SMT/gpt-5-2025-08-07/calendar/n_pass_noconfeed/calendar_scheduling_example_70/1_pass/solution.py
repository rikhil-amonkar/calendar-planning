from z3 import Optimize, Int, Or

# Helper functions
def to_minutes(h, m):
    return h * 60 + m

def fmt_minutes(mm):
    h = mm // 60
    m = mm % 60
    return f"{h:02d}:{m:02d}"

# Problem setup
day = "Monday"
work_start = to_minutes(9, 0)
work_end = to_minutes(17, 0)
duration = 30  # minutes

# Busy intervals as [start, end) in minutes from midnight
busy = {
    "Denise": [
        (to_minutes(12, 0), to_minutes(12, 30)),
        (to_minutes(15, 30), to_minutes(16, 0)),
    ],
    "Angela": [
        # No meetings
    ],
    "Natalie": [
        (to_minutes(9, 0), to_minutes(11, 30)),
        (to_minutes(12, 0), to_minutes(13, 0)),
        (to_minutes(14, 0), to_minutes(14, 30)),
        (to_minutes(15, 0), to_minutes(17, 0)),
    ],
}

# Z3 model
opt = Optimize()
start = Int("start")

# Constraints:
# - within working hours
opt.add(start >= work_start)
opt.add(start + duration <= work_end)

# - align to 30-minute boundaries
opt.add((start - work_start) % 30 == 0)

# - avoid all busy intervals
for person, intervals in busy.items():
    for s, e in intervals:
        opt.add(Or(start + duration <= s, start >= e))

# Preference: earliest availability
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s = model[start].as_long()
    e = s + duration
    time_range = f"{fmt_minutes(s)}:{fmt_minutes(e)}"
    # Output must include both the time range and the day of the week
    print(day)
    print(f"{{{time_range}}}")
else:
    print("No feasible meeting time found.")