import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 1 hour long, so start_time must be between 0 and 420 (inclusive)
solver.add(start_time >= 0)
solver.add(start_time <= 420)

# Julie's blocked intervals
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 60 <= 0, start_time >= 30))
# 11:00-11:30 (120-150)
solver.add(z3.Or(start_time + 60 <= 120, start_time >= 150))
# 12:00-12:30 (180-210)
solver.add(z3.Or(start_time + 60 <= 180, start_time >= 210))
# 13:30-14:00 (270-300)
solver.add(z3.Or(start_time + 60 <= 270, start_time >= 300))
# 16:00-17:00 (420-480)
solver.add(z3.Or(start_time + 60 <= 420, start_time >= 480))

# Sean's blocked intervals
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 60 <= 0, start_time >= 30))
# 13:00-13:30 (240-270)
solver.add(z3.Or(start_time + 60 <= 240, start_time >= 270))
# 15:00-15:30 (300-330)
solver.add(z3.Or(start_time + 60 <= 300, start_time >= 330))
# 16:00-16:30 (420-450)
solver.add(z3.Or(start_time + 60 <= 420, start_time >= 450))

# Lori's blocked intervals
# 10:00-10:30 (60-90)
solver.add(z3.Or(start_time + 60 <= 60, start_time >= 90))
# 11:00-13:00 (120-240)
solver.add(z3.Or(start_time + 60 <= 120, start_time >= 240))
# 15:30-17:00 (390-480)
solver.add(z3.Or(start_time + 60 <= 390, start_time >= 480))

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