import z3

# Initialize the Z3 solver
solver = z3.Solver()

# Define the start time variable in minutes after 9:00 AM
start_time = z3.Int('start_time')

# The meeting is 30 minutes long and must end by 11:00 AM (120 minutes after 9:00)
solver.add(start_time >= 0)
solver.add(start_time <= 90)  # start_time + 30 <= 120 => start_time <= 90

# Albert's first blocked interval: 9:00-10:00 (0-60 minutes)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 60))

# Albert's second blocked interval: 10:30-12:00 (90-150 minutes), but limited to 11:00 (120)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 120))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Convert start time to hours and minutes
    start_hour = 9 + (time_minutes // 60)
    start_min = time_minutes % 60
    
    # Calculate end time
    end_minutes = time_minutes + 30
    end_hour = 9 + (end_minutes // 60)
    end_min = end_minutes % 60
    
    print(f"Start: {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")