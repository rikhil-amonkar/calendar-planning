import z3

# Initialize Z3 solver
solver = z3.Solver()

# Define variables
day = z3.Int('day')  # 0 for Monday, 1 for Tuesday
start = z3.Int('start')  # in minutes since midnight

# Constraints for day and start time
solver.add(z3.Or(day == 0, day == 1))
solver.add(start >= 540, start <= 960)  # 9:00 to 16:00

# Gary's blocked intervals
gary_blocked = [
    (0, 570, 600),  # Monday 9:30-10:00
    (0, 660, 780),  # Monday 11:00-13:00
    (0, 840, 870),  # Monday 14:00-14:30
    (0, 990, 1020),  # Monday 16:30-17:00
    (1, 540, 570),  # Tuesday 9:00-9:30
    (1, 630, 660),  # Tuesday 10:30-11:00
    (1, 870, 960),  # Tuesday 14:30-16:00
]

# David's blocked intervals
david_blocked = [
    (0, 540, 570),  # Monday 9:00-9:30
    (0, 600, 780),  # Monday 10:00-13:00
    (0, 870, 990),  # Monday 14:30-16:30
    (1, 540, 570),  # Tuesday 9:00-9:30
    (1, 600, 630),  # Tuesday 10:00-10:30
    (1, 660, 750),  # Tuesday 11:00-12:30
    (1, 780, 870),  # Tuesday 13:00-14:30
    (1, 900, 960),  # Tuesday 15:00-16:00
    (1, 990, 1020),  # Tuesday 16:30-17:00
]

# Combine all blocked intervals
all_blocked = gary_blocked + david_blocked

# Add constraints for each blocked interval
for d, bs, be in all_blocked:
    solver.add(z3.Implies(day == d, z3.Or(start + 60 <= bs, start >= be)))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = start_val + 60

    def to_time_str(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    day_str = "Monday" if day_val == 0 else "Tuesday"
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")
else:
    print("No solution found.")