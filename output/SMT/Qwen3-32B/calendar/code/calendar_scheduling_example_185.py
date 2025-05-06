import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 30 minutes long, work hours from 9:00 AM to 5:00 PM (0 to 480 minutes)
# Start time must be between 0 and 450 (since 450 + 30 = 480)
solver.add(start_time >= 0)
solver.add(start_time <= 450)

# Kimberly's constraints
# 10:00-10:30 (60-90)
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 90))
# 11:00-12:00 (120-180)
solver.add(z3.Or(start_time + 30 <= 120, start_time >= 180))
# 16:00-16:30 (420-450)
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 450))

# Megan's preference: avoid before 10:00 (60 minutes)
solver.add(start_time >= 60)

# Marie's constraints
# 10:00-11:00 (60-120)
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 120))
# 11:30-15:00 (150-330)
solver.add(z3.Or(start_time + 30 <= 150, start_time >= 330))
# 16:00-16:30 (420-450)
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 450))

# Diana's constraints
# 9:30-10:00 (30-60)
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 60))
# 10:30-14:30 (90-330)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 330))
# 15:30-17:00 (390-480)
solver.add(start_time <= 360)  # start + 30 <= 390 => start <= 360

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