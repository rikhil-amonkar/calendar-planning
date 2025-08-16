import z3

# Define busy times for Diane and Matthew in minutes since midnight
diane_busy = [
    # Monday
    [(720, 750), (900, 930)],
    # Tuesday
    [(600, 660), (690, 720), (750, 780), (960, 1020)],
    # Wednesday
    [(540, 570), (870, 900), (990, 1020)],
    # Thursday
    [(930, 990)],
    # Friday
    [(570, 690), (870, 900), (960, 1020)]
]

matthew_busy = [
    # Monday
    [(540, 600), (630, 1020)],
    # Tuesday
    [(540, 1020)],
    # Wednesday
    [(540, 660), (720, 870), (960, 1020)],
    # Thursday
    [(540, 960)],
    # Friday
    [(540, 1020)]
]

solver = z3.Solver()

day = z3.Int('day')
start = z3.Int('start')

# Constraints on day and start time
solver.add(z3.And(0 <= day, day <= 4))
solver.add(z3.And(540 <= start, start <= 960))

# Add Diane's constraints
for d in range(5):
    for (s, e) in diane_busy[d]:
        solver.add(z3.Implies(day == d, z3.Or(start + 60 <= s, start >= e)))

# Add Matthew's constraints
for d in range(5):
    for (s, e) in matthew_busy[d]:
        solver.add(z3.Implies(day == d, z3.Or(start + 60 <= s, start >= e)))

# Add Matthew's preference
solver.add(z3.Implies(day == 2, start >= 750))  # Wednesday is day 2, 12:30 is 750 minutes

if solver.check() == z3.sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 60

    # Convert day to name
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    day_name = days[day_val]

    # Convert start and end times to HH:MM format
    def to_time(m):
        h = m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(end_val)}")
else:
    print("No solution found.")