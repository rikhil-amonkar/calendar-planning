from z3 import Optimize, Int, Or

def hm(h, m):
    return h * 60 + m

def minutes_to_str(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Problem data
day = "Monday"
work_start = hm(9, 0)
work_end = hm(17, 0)
duration = 60  # minutes

# Existing schedules (half-open intervals [start, end))
schedules = {
    "Danielle": [
        (hm(9, 0), hm(10, 0)),
        (hm(10, 30), hm(11, 0)),
        (hm(14, 30), hm(15, 0)),
        (hm(15, 30), hm(16, 0)),
        (hm(16, 30), hm(17, 0)),
    ],
    "Bruce": [
        (hm(11, 0), hm(11, 30)),
        (hm(12, 30), hm(13, 0)),
        (hm(14, 0), hm(14, 30)),
        (hm(15, 30), hm(16, 0)),
    ],
    "Eric": [
        (hm(9, 0), hm(9, 30)),
        (hm(10, 0), hm(11, 0)),
        (hm(11, 30), hm(13, 0)),
        (hm(14, 30), hm(15, 30)),
    ],
}

# Z3 model
opt = Optimize()
start = Int("start")
end = start + duration

# Work hours constraint
opt.add(start >= work_start, end <= work_end)

# Non-overlap constraints for each participant's busy intervals
for person, intervals in schedules.items():
    for (b_start, b_end) in intervals:
        # Meeting [start, end) does not overlap busy [b_start, b_end)
        opt.add(Or(end <= b_start, start >= b_end))

# Prefer the earliest feasible start time
opt.minimize(start)

if opt.check() != sat:
    # As per problem statement, a solution exists; this branch should not occur.
    raise RuntimeError("No feasible schedule found.")

model = opt.model()
start_min = model[start].as_long()
end_min = start_min + duration

print("SOLUTION:")
print(f"Day: {day}")
print(f"Start Time: {minutes_to_str(start_min)}")
print(f"End Time: {minutes_to_str(end_min)}")