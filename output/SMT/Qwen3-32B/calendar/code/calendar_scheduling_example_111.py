import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 30 minutes long, work hours from 9:00 AM to 5:00 PM (0 to 480 minutes)
# Start time must be between 0 and 450 (since 450 + 30 = 480)
solver.add(start_time >= 0)
solver.add(start_time <= 450)

# Gregory's constraints
# 9:00-10:00 (0-60)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 60))
# 10:30-11:30 (90-150)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 150))
# 12:30-13:00 (210-240)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 240))
# 13:30-14:00 (270-300)
solver.add(z3.Or(start_time + 30 <= 270, start_time >= 300))

# Christine's constraints
# 9:00-11:30 (0-150)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 150))
# 13:30-17:00 (270-480)
solver.add(z3.Or(start_time + 30 <= 270, start_time >= 480))

# Vincent's constraints
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))
# 10:30-12:00 (90-180)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 180))
# 12:30-14:00 (210-300)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 300))
# 14:30-17:00 (330-480)
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 480))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Convert to 24-hour format
    start_hour = 9 + (time_minutes // 60)
    start_min = time_minutes % 60
    end_hour = start_hour
    end_min = start_min + 30
    if end_min == 60:
        end_hour += 1
        end_min = 0
    
    print(f"Start: {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")