import z3

# Initialize solver
solver = z3.Solver()

# Define start time as an integer (minutes since midnight)
S = z3.Int('S')

# Work hours are 9:00 (540) to 17:00 (1020)
# Meeting is 30 minutes, so start time must be <= 990 (16:30)
solver.add(S >= 540)
solver.add(S <= 990)

# Jeffrey's busy intervals (minutes since midnight)
jeffrey_busy = [(570, 600), (630, 660)]
for b_start, b_end in jeffrey_busy:
    solver.add(z3.Or(S + 30 <= b_start, S >= b_end))

# Virginia's busy intervals
virginia_busy = [(540, 570), (600, 630), (870, 900), (960, 990)]
for b_start, b_end in virginia_busy:
    solver.add(z3.Or(S + 30 <= b_start, S >= b_end))

# Melissa's busy intervals
melissa_busy = [(540, 690), (720, 750), (780, 900), (960, 1020)]
for b_start, b_end in melissa_busy:
    solver.add(z3.Or(S + 30 <= b_start, S >= b_end))

# Melissa's preference: meeting ends by 14:00 (840 minutes)
solver.add(S + 30 <= 840)

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    start = model[S].as_long()
    end = start + 30

    # Convert minutes to HH:MM format
    def to_time_str(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {to_time_str(start)}")
    print(f"End Time: {to_time_str(end)}")
else:
    print("No solution found")