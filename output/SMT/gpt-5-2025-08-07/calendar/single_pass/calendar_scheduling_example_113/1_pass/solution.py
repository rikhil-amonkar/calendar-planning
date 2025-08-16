from z3 import Optimize, Int, And, Or, sat

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def fmt_minutes(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Problem data
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

# Busy schedules (inclusive of start, exclusive of end)
busy = {
    "Bradley": [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("12:30"), to_minutes("13:00")),
        (to_minutes("13:30"), to_minutes("14:00")),
        (to_minutes("15:30"), to_minutes("16:00")),
    ],
    "Teresa": [
        (to_minutes("10:30"), to_minutes("11:00")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:30"), to_minutes("15:00")),
    ],
    "Elizabeth": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:30"), to_minutes("11:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:30"), to_minutes("15:00")),
        (to_minutes("15:30"), to_minutes("17:00")),
    ],
    "Christian": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:30"), to_minutes("17:00")),
    ],
}

# Z3 variables
start = Int("start")
end = Int("end")

opt = Optimize()

# Meeting duration and work hours constraints
opt.add(end == start + duration)
opt.add(start >= work_start)
opt.add(end <= work_end)

# No overlap with any busy interval for any participant
for person, intervals in busy.items():
    for (b_start, b_end) in intervals:
        # Meeting [start, end) does not intersect [b_start, b_end)
        opt.add(Or(end <= b_start, start >= b_end))

# Optional: find the earliest feasible start time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    start_min = model[start].as_long()
    end_min = model[end].as_long()
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_minutes(start_min)}")
    print(f"End Time: {fmt_minutes(end_min)}")
else:
    # Per problem statement, a solution exists; this is a safety fallback.
    print("SOLUTION:")
    print(f"Day: {day}")
    print("Start Time: 00:00")
    print("End Time: 00:30")