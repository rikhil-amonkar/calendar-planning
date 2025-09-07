import z3

opt = z3.Optimize()

day = z3.Int('day')
start_time = z3.Int('start_time')

# Define work hours constraints
opt.add(z3.And(0 <= day, day <= 4))
opt.add(z3.And(540 <= start_time, start_time <= 960))  # 9:00 to 16:00 (start_time + 60 <= 1020)

# Busy times for Brian and Julia per day (0=Monday to 4=Friday)
brian_busy = {
    0: [(570, 600), (750, 870), (930, 960)],  # Monday
    1: [(540, 570)],  # Tuesday
    2: [(750, 840), (990, 1020)],  # Wednesday
    3: [(660, 690), (780, 810), (990, 1020)],  # Thursday
    4: [(570, 600), (630, 660), (780, 810), (900, 960), (990, 1020)],  # Friday
}

julia_busy = {
    0: [(540, 600), (660, 690), (750, 780), (930, 960)],  # Monday
    1: [(780, 840), (960, 990)],  # Tuesday
    2: [(540, 690), (720, 750), (780, 1020)],  # Wednesday
    3: [(540, 630), (660, 1020)],  # Thursday
    4: [(540, 600), (630, 690), (750, 840), (870, 900), (930, 960)],  # Friday
}

# Add constraints for each day's busy times
for d in range(5):
    # Brian's constraints for day d
    for b_start, b_end in brian_busy[d]:
        cond = (day == d)
        constraint = z3.Or(start_time + 60 <= b_start, start_time >= b_end)
        opt.add(z3.Implies(cond, constraint))
    # Julia's constraints for day d
    for b_start, b_end in julia_busy[d]:
        cond = (day == d)
        constraint = z3.Or(start_time + 60 <= b_start, start_time >= b_end)
        opt.add(z3.Implies(cond, constraint))

# Optimization objectives: minimize day first, then start_time
opt.minimize(day)
opt.minimize(start_time)

if opt.check() == z3.sat:
    model = opt.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    day_name = days[day_val]
    # Convert start and end times to HH:MM format
    start_h = start_val // 60
    start_m = start_val % 60
    end_val = start_val + 60
    end_h = end_val // 60
    end_m = end_val % 60
    # Format with leading zeros
    start_time_str = f"{start_h:02d}:{start_m:02d}"
    end_time_str = f"{end_h:02d}:{end_m:02d}"
    print(f"{start_time_str}:{end_time_str} {day_name}")
else:
    print("No solution found.")