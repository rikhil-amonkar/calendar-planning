# Requires: z3-solver
from z3 import Optimize, Int, Or

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Meeting parameters
day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 30  # minutes

# Busy schedules (half-open intervals [start, end))
busy = {
    "Natalie": [],
    "David": [
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
    ],
    "Douglas": [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
    ],
    "Ralph": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00")),
    ],
    "Jordan": [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00")),
    ],
}

# Preference: David does not want to meet before 14:00
david_pref_start = time_to_minutes("14:00")

opt = Optimize()
start = Int("start")
end = start + duration

# Work hours constraints
opt.add(start >= work_start)
opt.add(end <= work_end)

# Preference constraint
opt.add(start >= david_pref_start)

# No-overlap with all busy intervals
for person, intervals in busy.items():
    for (bs, be) in intervals:
        # Meeting [start, end) must be disjoint from [bs, be)
        opt.add(Or(end <= bs, start >= be))

# Optionally find the earliest valid time
opt.minimize(start)

if opt.check() == 1:  # sat
    m = opt.model()
    s_val = m.eval(start).as_long()
    e_val = s_val + duration
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {minutes_to_time(s_val)}")
    print(f"End Time: {minutes_to_time(e_val)}")
else:
    # Given the problem statement guarantees a solution, this shouldn't happen.
    raise RuntimeError("No feasible meeting time found.")