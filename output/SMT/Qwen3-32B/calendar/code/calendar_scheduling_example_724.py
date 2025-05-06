import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Work hours from Monday 9:00 to 17:00 (0-480 minutes)
# Meeting is 30 minutes, so start_time must be between 0 and 450
solver.add(start_time >= 0)
solver.add(start_time <= 450)

# Ruth's Monday constraints
# 9:00-10:00 (0-60)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 60))
# 10:30-12:00 (90-180)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 180))
# 12:30-14:30 (210-330)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 330))
# 15:00-16:00 (360-420)
solver.add(z3.Or(start_time + 30 <= 360, start_time >= 420))
# 16:30-17:00 (450-480)
solver.add(z3.Or(start_time + 30 <= 450, start_time >= 480))

# Tyler's preference: avoid Monday before 16:00 (420 minutes)
solver.add(start_time >= 420)

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