import z3

# Initialize solver
solver = z3.Solver()
start = z3.Int('start')

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes, so latest start time is 16:30 (990 minutes)
solver.add(start >= 540, start <= 990)

# Collect all busy intervals in minutes since midnight
busy_intervals = []

# Andrea's busy times
busy_intervals.extend([(570, 630), (810, 870)])
# Ruth's busy times
busy_intervals.extend([(750, 780), (900, 930)])
# Steven's busy times
busy_intervals.extend([(600, 630), (660, 690), (720, 750), (810, 840), (900, 960)])
# Kyle's busy times
busy_intervals.extend([(540, 570), (630, 720), (750, 780), (810, 900), (930, 960), (990, 1020)])
# Elijah's busy times
busy_intervals.extend([(540, 660), (690, 780), (810, 840), (930, 960), (990, 1020)])
# Lori's busy times
busy_intervals.extend([(540, 570), (600, 690), (720, 810), (840, 960), (990, 1020)])

# Add constraints for each busy interval
for b_start, b_end in busy_intervals:
    solver.add(z3.Or(start + 30 <= b_start, start >= b_end))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    start_time = model[start].as_long()
    # Convert start_time to HH:MM format
    start_h, start_m = divmod(start_time, 60)
    end_time = start_time + 30
    end_h, end_m = divmod(end_time, 60)
    start_str = f"{start_h:02d}:{start_m:02d}"
    end_str = f"{end_h:02d}:{end_m:02d}"
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {start_str}")
    print(f"End Time: {end_str}")
else:
    print("No solution found.")