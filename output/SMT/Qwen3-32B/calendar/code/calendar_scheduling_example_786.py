import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Time range constraints (0 to 1410 minutes since Monday 9:00 AM)
solver.add(start_time >= 0)
solver.add(start_time <= 1410)

# Avoid Monday
solver.add(start_time > 450)

# Tuesday and Wednesday preference constraints
solver.add(z3.Implies(z3.And(start_time >= 480, start_time <= 960), start_time >= 900))
solver.add(z3.Implies(z3.And(start_time >= 960, start_time <= 1440), start_time >= 1380))

# Amy's constraints on Wednesday
solver.add(z3.Implies(z3.And(start_time >= 960, start_time <= 1440), 
    z3.And(
        z3.Or(start_time + 30 <= 1080, start_time >= 1110),  # 11:00-11:30
        z3.Or(start_time + 30 <= 1230, start_time >= 1260)   # 13:30-14:00
    )
))

# Pamela's constraints on Wednesday
solver.add(z3.Implies(z3.And(start_time >= 960, start_time <= 1440), 
    z3.Or(start_time + 30 <= 1380, start_time >= 1410)  # 16:00-16:30
))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Determine day and offset
    if 480 <= time_minutes <= 960:
        day = "Tuesday"
        offset = time_minutes - 480
    elif 960 <= time_minutes <= 1440:
        day = "Wednesday"
        offset = time_minutes - 960
    else:
        day = "Unknown"
        offset = 0  # Should not happen
    
    start_hour = 9 + (offset // 60)
    start_min = offset % 60
    end_hour = start_hour
    end_min = start_min + 30
    if end_min == 60:
        end_hour += 1
        end_min = 0
    
    print(f"Start: {day} {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")