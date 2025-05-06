import z3

# Initialize the Z3 solver
solver = z3.Solver()

# Define the start time variable in minutes after 9:00 AM
start_time = z3.Int('start_time')

# The meeting is 30 minutes long and must end by 17:00 (480 minutes after 9:00)
solver.add(start_time >= 0)
solver.add(start_time <= 450)  # start_time + 30 <= 480 => start_time <= 450

# Doris's blocked intervals
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 120))  # 9:00-11:00
solver.add(z3.Or(start_time + 30 <= 270, start_time >= 300))  # 13:30-14:00
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 450))  # 16:00-16:30

# Theresa's blocked interval
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 180))  # 10:00-12:00

# Terry's blocked intervals
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 60))  # 9:30-10:00
solver.add(z3.Or(start_time + 30 <= 150, start_time >= 180))  # 11:30-12:00
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 240))  # 12:30-13:00
solver.add(z3.Or(start_time + 30 <= 270, start_time >= 300))  # 13:30-14:00
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 360))  # 14:30-15:00
solver.add(z3.Or(start_time + 30 <= 450, start_time >= 540))  # 15:30-17:00

# Carolyn's blocked intervals
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 150))  # 9:00-10:30
solver.add(z3.Or(start_time + 30 <= 120, start_time >= 150))  # 11:00-11:30
solver.add(z3.Or(start_time + 30 <= 180, start_time >= 240))  # 12:00-13:00
solver.add(z3.Or(start_time + 30 <= 270, start_time >= 330))  # 13:30-14:30
solver.add(z3.Or(start_time + 30 <= 360, start_time >= 480))  # 15:00-17:00

# Kyle's blocked intervals
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))  # 9:00-9:30
solver.add(z3.Or(start_time + 30 <= 150, start_time >= 180))  # 11:30-12:00
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 240))  # 12:30-13:00
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 480))  # 14:30-17:00

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