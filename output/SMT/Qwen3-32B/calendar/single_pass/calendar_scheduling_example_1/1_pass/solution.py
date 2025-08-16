import z3

# Initialize solver
solver = z3.Solver()

# Define start time variable (in minutes since midnight)
start = z3.Int('start')

# Work hours are from 9:00 (540) to 17:00 (1020), meeting is 30 minutes
solver.add(start >= 540)  # 9:00 AM
solver.add(start <= 990)  # 17:00 - 30 minutes = 16:30 (990)

# Raymond's blocked intervals (in minutes since midnight)
raymond_blocked = [(540, 570), (690, 720), (780, 810), (900, 930)]
for s, e in raymond_blocked:
    solver.add(z3.Or(start + 30 <= s, e <= start))

# Billy's blocked intervals
billy_blocked = [(600, 630), (720, 780), (990, 1020)]
for s, e in billy_blocked:
    solver.add(z3.Or(start + 30 <= s, e <= start))

# Donald's blocked intervals
donald_blocked = [(540, 570), (600, 660), (720, 780), (840, 870), (960, 1020)]
for s, e in donald_blocked:
    solver.add(z3.Or(start + 30 <= s, e <= start))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    start_val = model[start].as_long()
    
    # Convert start_val to HH:MM format
    start_hours = start_val // 60
    start_minutes = start_val % 60
    end_val = start_val + 30
    end_hours = end_val // 60
    end_minutes = end_val % 60
    
    start_time = f"{start_hours:02d}:{start_minutes:02d}"
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")
else:
    print("No solution found.")