import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 30 minutes long, so start_time must be between 0 and 450 (inclusive)
solver.add(start_time >= 0)
solver.add(start_time <= 450)

# Stephanie's blocked intervals
solver.add(z3.Or(start_time + 30 <= 120, start_time >= 150))  # 11:00-11:30 (120-150)
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 360))  # 14:30-15:00 (330-360)

# Joe's blocked intervals
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))     # 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 180))   # 10:00-12:00 (60-180)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 240))  # 12:30-13:00 (210-240)
solver.add(z3.Or(start_time + 30 <= 300, start_time >= 480))  # 14:00-17:00 (300-480)

# Diana's blocked intervals
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 90))     # 9:00-10:30 (0-90)
solver.add(z3.Or(start_time + 30 <= 150, start_time >= 180))  # 11:30-12:00 (150-180)
solver.add(z3.Or(start_time + 30 <= 240, start_time >= 300))  # 13:00-14:00 (240-300)
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 390))  # 14:30-15:30 (330-390)
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 480))  # 16:00-17:00 (420-480)

# Deborah's blocked intervals
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 60))     # 9:00-10:00 (0-60)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 180))   # 10:30-12:00 (90-180)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 240))  # 12:30-13:00 (210-240)
solver.add(z3.Or(start_time + 30 <= 270, start_time >= 300))  # 13:30-14:00 (270-300)
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 390))  # 14:30-15:30 (330-390)
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 450))  # 16:00-16:30 (420-450)

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