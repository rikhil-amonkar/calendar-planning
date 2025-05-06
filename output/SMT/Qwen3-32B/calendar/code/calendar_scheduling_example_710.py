import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Valid time ranges for Monday, Tuesday, and Wednesday
solver.add(z3.Or(
    z3.And(start_time >= 0, start_time <= 450),  # Monday
    z3.And(start_time >= 480, start_time <= 930),  # Tuesday
    z3.And(start_time >= 960, start_time <= 1410)  # Wednesday
))

# Cheryl cannot meet on Wednesday
solver.add(start_time < 960)

# Cheryl's Monday constraints
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 90))  # 9:00-9:30
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 270))  # 11:30-13:00
solver.add(z3.Or(start_time + 30 <= 450, start_time >= 480))  # 15:30-16:00

# Cheryl's Tuesday constraints
solver.add(z3.Or(start_time + 30 <= 840, start_time >= 870))  # 15:00-15:30

# Kyle's Monday constraints (busy all day)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 480))

# Kyle's Tuesday constraints (busy from 9:30 AM to 17:00)
solver.add(z3.Or(start_time + 30 <= 510, start_time >= 960))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    if 0 <= time_minutes <= 450:
        day = "Monday"
        offset = time_minutes
    elif 480 <= time_minutes <= 930:
        day = "Tuesday"
        offset = time_minutes - 480
    else:
        day = "Wednesday"
        offset = time_minutes - 960
    
    start_hour = 9 + (offset // 60)
    start_min = offset % 60
    end_offset = offset + 30
    end_hour = 9 + (end_offset // 60)
    end_min = end_offset % 60
    
    print(f"Start: {day} {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")