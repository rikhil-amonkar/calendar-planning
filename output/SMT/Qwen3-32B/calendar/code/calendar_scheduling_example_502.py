import z3

# Initialize the Z3 solver
solver = z3.Solver()

# Define the start time variable in minutes after 9:00 AM
start_time = z3.Int('start_time')

# The meeting is 30 minutes long and must end by 17:00 (480 minutes after 9:00)
solver.add(start_time >= 0)
solver.add(start_time <= 450)  # start_time + 30 <= 480 => start_time <= 450

# Jack's busy intervals
# 9:30-10:30 (30-90)
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 90))
# 11:00-11:30 (120-150)
solver.add(z3.Or(start_time + 30 <= 120, start_time >= 150))
# 12:30-13:00 (210-240)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 240))
# 14:00-14:30 (240-270)
solver.add(z3.Or(start_time + 30 <= 240, start_time >= 270))
# 16:00-16:30 (360-390)
solver.add(z3.Or(start_time + 30 <= 360, start_time >= 390))

# Charlotte's busy intervals
# 9:30-10:00 (30-60)
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 60))
# 10:30-12:00 (90-180)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 180))
# 12:30-13:30 (210-270)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 270))
# 14:00-16:00 (240-360)
solver.add(z3.Or(start_time + 30 <= 240, start_time >= 360))

# Jack's preference: avoid meetings after 12:30 (210 minutes)
solver.add(start_time <= 210)

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Convert to 24-hour format
    start_hour = 9 + (time_minutes // 60)
    start_min = time_minutes % 60
    end_minutes = time_minutes + 30
    end_hour = 9 + (end_minutes // 60)
    end_min = end_minutes % 60
    
    print(f"Start: {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")