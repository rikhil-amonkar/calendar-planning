from z3 import *

# Define busy times for Betty and Megan
busy_betty = {
    0: [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    1: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30), (13 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
    2: [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)],
    4: [(9 * 60, 10 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60 + 30, 15 * 60)]
}

busy_megan = {
    0: [(9 * 60, 17 * 60)],
    1: [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (12 * 60, 14 * 60), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    2: [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (13 * 60, 14 * 60 + 30), (15 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],
    4: [(9 * 60, 17 * 60)]
}

# Initialize solver
solver = Solver()

# Variables
day = Int('day')
start_time = Int('start_time')

# Day must be Monday (0), Tuesday (1), or Friday (4)
solver.add(Or(day == 0, day == 1, day == 4))

# Start time between 9:00 (540) and 16:00 (960)
solver.add(start_time >= 9 * 60)
solver.add(start_time <= 16 * 60)

# Add constraints for each day and busy intervals
for D in [0, 1, 4]:
    for (b_start, b_end) in busy_betty.get(D, []):
        cond = Or(start_time + 60 <= b_start, start_time >= b_end)
        solver.add(Implies(day == D, cond))
    for (b_start, b_end) in busy_megan.get(D, []):
        cond = Or(start_time + 60 <= b_start, start_time >= b_end)
        solver.add(Implies(day == D, cond))

# Check solution
if solver.check() == sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start_time].as_long()
    end_val = start_val + 60

    # Convert day to name
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    day_name = days[day_val]

    # Convert time to HH:MM format
    def to_time(mins):
        hours = mins // 60
        mins_remaining = mins % 60
        return f"{hours:02d}:{mins_remaining:02d}"

    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {to_time(start_val)}")
    print(f"End Time: {to_time(end_val)}")
else:
    print("No solution found.")