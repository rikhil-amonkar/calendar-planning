from z3 import Int, Optimize, Or

def minutes(h, m):
    return h * 60 + m

# Problem data
day = "Monday"
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 30  # minutes

# Busy schedules (start, end) in minutes from 00:00
lisa_busy = [
    (minutes(9, 0),  minutes(9, 30)),
    (minutes(10, 30), minutes(11, 0)),
    (minutes(14, 0), minutes(16, 0)),
]

anthony_busy = [
    (minutes(9, 0),  minutes(9, 30)),
    (minutes(11, 0), minutes(11, 30)),
    (minutes(12, 30), minutes(13, 30)),
    (minutes(14, 0), minutes(15, 0)),
    (minutes(15, 30), minutes(16, 0)),
    (minutes(16, 30), minutes(17, 0)),
]

# Z3 model
start = Int("start")
end = start + duration

opt = Optimize()

# Work hours constraint
opt.add(start >= work_start, end <= work_end)

# Non-overlap with busy times
def add_non_overlap_constraints(busy_list):
    for (b_start, b_end) in busy_list:
        # Meeting does not overlap: [start, end) and [b_start, b_end) are disjoint
        opt.add(Or(end <= b_start, start >= b_end))

add_non_overlap_constraints(lisa_busy)
add_non_overlap_constraints(anthony_busy)

# Preference: earliest possible start time
opt.minimize(start)

if opt.check() !=  sat:
    raise RuntimeError("No solution found, but the problem statement guarantees one exists.")

model = opt.model()
start_min = model[start].as_long()
end_min = start_min + duration

def fmt(mm):
    h = mm // 60
    m = mm % 60
    return f"{h:02d}:{m:02d}"

print("SOLUTION:")
print(f"Day: {day}")
print(f"Start Time: {fmt(start_min)} (24-hour format)")
print(f"End Time: {fmt(end_min)} (24-hour format)")