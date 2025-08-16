import z3

# Initialize Z3 solver
solver = z3.Solver()

# Define start time as an integer variable (minutes since midnight)
start = z3.Int('start')

# Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
# Meeting duration is 30 minutes, so start must be <= 990 (16:30)
solver.add(start >= 540)
solver.add(start <= 990)

# Define busy intervals for each participant in minutes since midnight
busy_times = {
    'Jacob': [(810, 840), (870, 900)],
    'Diana': [(570, 600), (690, 720), (780, 810), (960, 990)],
    'Adam': [(570, 630), (660, 750), (930, 960)],
    'Angela': [(570, 600), (630, 720), (780, 930), (960, 990)],
    'Dennis': [(540, 570), (630, 690), (780, 900), (990, 1020)]
}

# Add constraints to avoid overlapping with each busy interval
for intervals in busy_times.values():
    for (busy_start, busy_end) in intervals:
        solver.add(z3.Or(start + 30 <= busy_start, start >= busy_end))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    end_val = start_val + 30
    day = "Monday"
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_val // 60:02d}:{start_val % 60:02d}")
    print(f"End Time: {end_val // 60:02d}:{end_val % 60:02d}")
else:
    print("No solution found.")