import z3

# Initialize solver
solver = z3.Solver()

# Define variables
day = z3.Int('day')
start = z3.Int('start')
end = start + 30

# Basic constraints
solver.add(z3.Or(day == 0, day == 1, day == 2))  # Monday, Tuesday, Wednesday
solver.add(start >= 540)  # 9:00 AM
solver.add(start <= 990)  # 16:30 (since meeting duration is 30 min)

# Amy's busy times: only on Wednesday (day 2)
amy_busy = [
    (2, [(660, 690), (810, 840)]),
]
for d, intervals in amy_busy:
    constraints = []
    for bs, be in intervals:
        constraints.append(z3.Or(start + 30 <= bs, start >= be))
    solver.add(z3.Implies(day == d, z3.And(constraints)))

# Pamela's busy times
pamela_busy = [
    (0, [(540, 630), (660, 990)]),  # Monday
    (1, [(540, 570), (600, 1020)]),  # Tuesday
    (2, [(540, 570), (600, 660), (690, 810), (870, 900), (960, 990)]),  # Wednesday
]
for d, intervals in pamela_busy:
    constraints = []
    for bs, be in intervals:
        constraints.append(z3.Or(start + 30 <= bs, start >= be))
    solver.add(z3.Implies(day == d, z3.And(constraints)))

# Preference constraints
solver.add(day != 0)  # Avoid Monday
solver.add(z3.Implies(day == 2, start >= 960))  # On Wednesday, avoid before 16:00

if solver.check() == z3.sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 30

    # Map day to string
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_str = days[day_val]

    # Convert time to HH:MM format
    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(end_val)}")
else:
    print("No solution found")