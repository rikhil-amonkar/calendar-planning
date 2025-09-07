import z3

def to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

# Define busy intervals in minutes
ronald_busy = {
    0: [(630, 660), (720, 750), (930, 960)],
    1: [(540, 570), (720, 750), (930, 990)],
    2: [(570, 630), (660, 720), (750, 780), (810, 840), (990, 1020)]
}

amber_busy = {
    0: [(540, 570), (600, 630), (690, 720), (750, 840), (870, 900), (930, 1020)],
    1: [(540, 570), (600, 690), (720, 750), (810, 930), (990, 1020)],
    2: [(540, 570), (600, 630), (660, 810), (900, 930)]
}

opt = z3.Optimize()

day = z3.Int('day')
start_time = z3.Int('start_time')

# Constraints for day and start_time
opt.add(z3.Or(day == 0, day == 1, day == 2))
opt.add(z3.And(start_time >= 540, start_time <= 990))  # 9:00-17:00 minus 30 min for duration

# For each day, add constraints for busy intervals of Ronald and Amber
for d in ronald_busy:
    for b_start, b_end in ronald_busy[d]:
        opt.add(z3.Implies(day == d, z3.Or(start_time + 30 <= b_start, start_time >= b_end)))

for d in amber_busy:
    for b_start, b_end in amber_busy[d]:
        opt.add(z3.Implies(day == d, z3.Or(start_time + 30 <= b_start, start_time >= b_end)))

# Optimization: minimize day first, then start_time
opt.minimize(day)
opt.minimize(start_time)

if opt.check() == z3.sat:
    model = opt.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    end_val = start_val + 30
    day_name = ['Monday', 'Tuesday', 'Wednesday'][day_val]
    start_str = to_time(start_val)
    end_str = to_time(end_val)
    print(f"{day_name} {start_str}:{end_str}")
else:
    print("No solution found")