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

# Nancy's blocked intervals on Monday
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 90))  # 10:00-10:30
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 270))  # 11:30-12:30
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 360))  # 13:30-14:00
solver.add(z3.Or(start_time + 30 <= 390, start_time >= 450))  # 14:30-15:30
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 480))  # 16:00-17:00

# Nancy's blocked intervals on Tuesday
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 90))  # 9:30-10:30
solver.add(z3.Or(start_time + 30 <= 120, start_time >= 150))  # 11:00-11:30
solver.add(z3.Or(start_time + 30 <= 150, start_time >= 180))  # 12:00-12:30
solver.add(z3.Or(start_time + 30 <= 180, start_time >= 210))  # 13:00-13:30
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 360))  # 15:30-16:00

# Nancy's blocked intervals on Wednesday
solver.add(z3.Or(start_time + 30 <= 1020, start_time >= 1110))  # 10:00-11:30
solver.add(z3.Or(start_time + 30 <= 1230, start_time >= 1380))  # 13:30-16:00

# Jose's blocked intervals on Monday (entire day)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 480))

# Jose's blocked intervals on Tuesday (entire day)
solver.add(z3.Or(start_time + 30 <= 480, start_time >= 960))

# Jose's blocked intervals on Wednesday
solver.add(z3.Or(start_time + 30 <= 960, start_time >= 990))  # 9:00-9:30
solver.add(z3.Or(start_time + 30 <= 1020, start_time >= 1170))  # 10:00-12:30
solver.add(z3.Or(start_time + 30 <= 1230, start_time >= 1290))  # 13:30-14:30
solver.add(z3.Or(start_time + 30 <= 1320, start_time >= 1440))  # 15:00-17:00

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    if time_minutes <= 450:
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