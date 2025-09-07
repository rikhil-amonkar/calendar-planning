import z3

day = z3.Int('day')
start = z3.Int('start')

solver = z3.Solver()

# Day must be Monday (0), Tuesday (1), or Friday (4)
solver.add(z3.Or(day == 0, day == 1, day == 4))

# Start time between 9:00 (540) and 16:00 (960)
solver.add(z3.And(start >= 540, start + 60 <= 1020))  # start + 60 <= 1020 => start <= 960

# Define Betty's busy intervals per day
betty_busy = {
    0: [(600, 630), (690, 750), (960, 990)],
    1: [(570, 600), (630, 660), (720, 750), (810, 900), (990, 1020)],
    4: [(540, 600), (690, 720), (750, 780), (870, 900)]
}

# Define Megan's busy intervals per day
megan_busy = {
    0: [(540, 1020)],
    1: [(540, 570), (600, 630), (720, 840), (900, 930), (960, 990)],
    4: [(540, 1020)]
}

# Add constraints for each day
for d in [0, 1, 4]:
    # Betty's constraints
    for (s, e) in betty_busy.get(d, []):
        solver.add(z3.Implies(day == d, z3.Or(start + 60 <= s, start >= e)))
    # Megan's constraints
    for (s, e) in megan_busy.get(d, []):
        solver.add(z3.Implies(day == d, z3.Or(start + 60 <= s, start >= e)))

if solver.check() == z3.sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    # Convert day number to day name
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    day_name = days[day_val]
    # Convert start time to HH:MM format
    start_hours = start_val // 60
    start_minutes = start_val % 60
    end_val = start_val + 60
    end_hours = end_val // 60
    end_minutes = end_val % 60
    # Format with leading zeros
    start_time = f"{start_hours:02d}:{start_minutes:02d}"
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    print(f"{day_name} {start_time}:{end_time}")
else:
    print("No solution found.")