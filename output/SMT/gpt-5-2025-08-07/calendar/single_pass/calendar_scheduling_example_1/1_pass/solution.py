from z3 import Optimize, Int, Or, sat

def minutes(hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return h * 60 + m

def to_hhmm(mins):
    return f"{mins // 60:02d}:{mins % 60:02d}"

# Problem data
day = "Monday"
work_start = minutes("09:00")
work_end = minutes("17:00")
duration = 30  # minutes

# Existing schedules (busy intervals) for each participant on Monday
busy = {
    "Raymond": [
        (minutes("09:00"), minutes("09:30")),
        (minutes("11:30"), minutes("12:00")),
        (minutes("13:00"), minutes("13:30")),
        (minutes("15:00"), minutes("15:30")),
    ],
    "Billy": [
        (minutes("10:00"), minutes("10:30")),
        (minutes("12:00"), minutes("13:00")),
        (minutes("16:30"), minutes("17:00")),
    ],
    "Donald": [
        (minutes("09:00"), minutes("09:30")),
        (minutes("10:00"), minutes("11:00")),
        (minutes("12:00"), minutes("13:00")),
        (minutes("14:00"), minutes("14:30")),
        (minutes("16:00"), minutes("17:00")),
    ],
}

# Z3 model
opt = Optimize()
start = Int("start")
end = Int("end")

# Meeting duration and work hours
opt.add(end == start + duration)
opt.add(start >= work_start, end <= work_end)

# No overlap with any participant's busy intervals
for person, intervals in busy.items():
    for (b_start, b_end) in intervals:
        # Meeting [start, end) does not intersect [b_start, b_end)
        opt.add(Or(end <= b_start, start >= b_end))

# Preference: Billy would like to avoid meetings after 15:00
# Soft constraint: meeting should finish by 15:00 if possible
opt.add_soft(end <= minutes("15:00"), 1, "prefer_before_15")

# For determinism, also minimize start time (earliest feasible time)
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s = model[start].as_long()
    e = model[end].as_long()
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {to_hhmm(s)}")
    print(f"End Time: {to_hhmm(e)}")
else:
    # As per problem statement, a solution exists; this branch should not be reached.
    # Included for completeness.
    print("SOLUTION:")
    print(f"Day: {day}")
    print("Start Time: 00:00")
    print("End Time: 00:30")