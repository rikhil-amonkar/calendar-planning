import z3

# Define the solver and variable
solver = z3.Solver()
s = z3.Int('s')

# Define work hours in minutes since midnight (9:00 to 16:30)
solver.add(s >= 9 * 60)  # 9:00 AM
solver.add(s <= 16 * 60 + 30)  # 4:30 PM

# List of busy intervals for each participant in minutes since midnight
busy_intervals = [
    # Gregory
    (9 * 60, 9 * 60 + 30), (11 * 60 + 30, 12 * 60),
    # Jonathan
    (9 * 60, 9 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60),
    # Barbara
    (10 * 60, 10 * 60 + 30), (13 * 60 + 30, 14 * 60),
    # Jesse
    (10 * 60, 11 * 60), (12 * 60 + 30, 14 * 60 + 30),
    # Alan
    (9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 15 * 60 + 30), (16 * 60, 17 * 60),
    # Nicole
    (9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 17 * 60),
    # Catherine
    (9 * 60, 10 * 60 + 30), (12 * 60, 13 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)
]

# Add constraints to avoid busy intervals
for b_start, b_end in busy_intervals:
    solver.add(z3.Or(s + 30 <= b_start, s >= b_end))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    s_val = model[s].as_long()
    # Convert start time to HH:MM format
    start_h = s_val // 60
    start_m = s_val % 60
    end_val = s_val + 30
    end_h = end_val // 60
    end_m = end_val % 60
    start_time = f"{start_h:02d}:{start_m:02d}"
    end_time = f"{end_h:02d}:{end_m:02d}"
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found")