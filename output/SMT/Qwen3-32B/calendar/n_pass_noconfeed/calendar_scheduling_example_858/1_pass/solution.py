import z3

# Define busy intervals for each participant and day (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday)
carl_busy = {
    0: [(660, 690)],  # Monday 11:00-11:30
    1: [(870, 900)],  # Tuesday 14:30-15:00
    2: [(600, 690), (780, 810)],  # Wednesday 10:00-11:30, 13:00-13:30
    3: [(810, 840), (960, 990)],  # Thursday 13:30-14:00, 16:00-16:30
}

margaret_busy = {
    0: [(540, 630), (660, 1020)],  # Monday 9:00-10:30, 11:00-17:00
    1: [(570, 720), (810, 840), (930, 1020)],  # Tuesday 9:30-12:00, 13:30-14:00, 15:30-17:00
    2: [(570, 720), (750, 780), (810, 870), (900, 1020)],  # Wednesday 9:30-12:00, 12:30-13:00, 13:30-14:30, 15:00-17:00
    3: [(600, 720), (750, 840), (870, 1020)],  # Thursday 10:00-12:00, 12:30-14:00, 14:30-17:00
}

# Z3 variables
d = z3.Int('d')  # day of the week (0-3)
s = z3.Int('s')  # start time in minutes since midnight

# Solver setup
opt = z3.Optimize()

# Constraints on day and start time
opt.add(z3.And(d >= 0, d <= 3))
opt.add(z3.And(s >= 540, s <= 960))  # 9:00 to 16:00 (inclusive)

# Add constraints for busy intervals
for day in range(4):
    for (b_start, b_end) in carl_busy[day] + margaret_busy[day]:
        opt.add(z3.Implies(d == day, z3.Or(s + 60 <= b_start, s >= b_end)))

# Minimize the day to prefer earlier days (avoid Thursday)
opt.minimize(d)

# Solve and output results
if opt.check() == z3.sat:
    model = opt.model()
    day_val = model[d].as_long()
    start_val = model[s].as_long()
    end_val = start_val + 60

    # Convert minutes to HH:MM format
    def to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    day_name = day_names[day_val]
    start_time = to_time(start_val)
    end_time = to_time(end_val)

    print(f"{start_time}:{end_time} {day_name}")
else:
    print("No solution found")