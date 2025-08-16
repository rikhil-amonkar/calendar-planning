import z3

# Initialize the solver
solver = z3.Solver()

# Define the start time as an integer (minutes since midnight)
start = z3.Int('start')

# Add constraints for the overall time window (9:00-17:00, 30-minute meeting)
solver.add(start >= 540)  # 9:00 AM
solver.add(start <= 990)  # 16:30 PM (start + 30 <= 1020 => start <= 990)

# Collect all busy intervals for all participants
all_busy_intervals = [
    # Megan's busy intervals
    (540, 570), (600, 660), (720, 750),
    # Christine's busy intervals
    (540, 570), (690, 720), (780, 840), (930, 990),
    # Sara's busy intervals
    (690, 720), (870, 900),
    # Bruce's busy intervals
    (570, 600), (630, 720), (750, 810), (870, 900), (930, 990),
    # Kathryn's busy intervals
    (600, 930), (960, 990),
    # Billy's busy intervals
    (540, 570), (660, 690), (720, 840), (870, 930)
]

# Add constraints to avoid overlapping with any busy intervals
for b_start, b_end in all_busy_intervals:
    solver.add(z3.Or(start + 30 <= b_start, start >= b_end))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    day = "Monday"
    start_time = f"{start_val // 60:02d}:{start_val % 60:02d}"
    end_time = f"{(start_val + 30) // 60:02d}:{(start_val + 30) % 60:02d}"
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")