import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 30 minutes long, work hours from 9:00 AM to 5:00 PM (0 to 480 minutes)
# Start time must be between 0 and 450 (since 450 + 30 = 480)
solver.add(start_time >= 0)
solver.add(start_time <= 450)

# Lisa's blocked intervals
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))
# 10:30-11:00 (90-120)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 120))
# 14:00-16:00 (300-420)
solver.add(z3.Or(start_time + 30 <= 300, start_time >= 420))

# Anthony's blocked intervals
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))
# 11:00-11:30 (120-150)
solver.add(z3.Or(start_time + 30 <= 120, start_time >= 150))
# 12:30-13:30 (210-270)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 270))
# 14:00-15:00 (300-360)
solver.add(z3.Or(start_time + 30 <= 300, start_time >= 360))
# 15:30-16:00 (390-420)
solver.add(z3.Or(start_time + 30 <= 390, start_time >= 420))
# 16:30-17:00 (450-480)
solver.add(z3.Or(start_time + 30 <= 450, start_time >= 480))

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