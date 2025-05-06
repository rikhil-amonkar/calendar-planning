import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 1 hour long, so start_time must be between 0 and 420 (inclusive)
solver.add(start_time >= 0)
solver.add(start_time <= 420)

# Anthony's constraints
# 9:30-10:00 (30-60)
solver.add(z3.Or(start_time + 60 <= 30, start_time >= 60))
# 12:00-13:00 (120-180)
solver.add(z3.Or(start_time + 60 <= 120, start_time >= 180))
# 16:00-16:30 (360-390)
solver.add(z3.Or(start_time + 60 <= 360, start_time >= 390))

# Pamela's constraints
# 9:30-10:00 (30-60)
solver.add(z3.Or(start_time + 60 <= 30, start_time >= 60))
# 16:30-17:00 and preference to end by 14:30 (330)
solver.add(start_time + 60 <= 330)  # start_time <= 270

# Zachary's constraints
# 9:00-11:30 (0-150)
solver.add(z3.Or(start_time + 60 <= 0, start_time >= 150))
# 12:00-12:30 (120-150)
solver.add(z3.Or(start_time + 60 <= 120, start_time >= 150))
# 13:00-13:30 (180-210)
solver.add(z3.Or(start_time + 60 <= 180, start_time >= 210))
# 14:30-15:00 (330-360)
solver.add(z3.Or(start_time + 60 <= 330, start_time >= 360))
# 16:00-17:00 (360-480)
solver.add(z3.Or(start_time + 60 <= 360, start_time >= 480))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Convert to 24-hour format
    start_hour = 9 + (time_minutes // 60)
    start_min = time_minutes % 60
    end_hour = start_hour
    end_min = start_min + 60
    if end_min == 60:
        end_hour += 1
        end_min = 0
    
    print(f"Start: {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")