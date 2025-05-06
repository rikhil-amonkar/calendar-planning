import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 30 minutes long, work hours from 9:00 AM to 5:00 PM (0 to 480 minutes)
# Start time must be between 0 and 450 (since 450 + 30 = 480)
solver.add(start_time >= 0)
solver.add(start_time <= 450)

# Megan's constraints
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))  # 9:00-9:30
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 120))  # 10:00-11:00
solver.add(z3.Or(start_time + 30 <= 180, start_time >= 210))  # 12:00-12:30

# Christine's constraints
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))  # 9:00-9:30
solver.add(z3.Or(start_time + 30 <= 150, start_time >= 180))  # 11:30-12:00
solver.add(z3.Or(start_time + 30 <= 240, start_time >= 300))  # 13:00-14:00
solver.add(z3.Or(start_time + 30 <= 390, start_time >= 450))  # 15:30-16:30

# Sara's constraints
solver.add(z3.Or(start_time + 30 <= 150, start_time >= 180))  # 11:30-12:00
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 360))  # 14:30-15:00

# Bruce's constraints
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 60))  # 9:30-10:00
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 180))  # 10:30-12:00
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 300))  # 12:30-14:00
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 360))  # 14:30-15:00
solver.add(z3.Or(start_time + 30 <= 390, start_time >= 450))  # 15:30-16:30

# Kathryn's constraints
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 390))  # 10:00-15:30
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 450))  # 16:00-16:30

# Billy's constraints
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))  # 9:00-9:30
solver.add(z3.Or(start_time + 30 <= 120, start_time >= 150))  # 11:00-11:30
solver.add(z3.Or(start_time + 30 <= 180, start_time >= 300))  # 12:00-14:00
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 390))  # 14:30-15:30

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