import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Work hours from Monday 9:00 to Wednesday 17:00 (0 to 1440 minutes)
# Meeting is 30 minutes, so start_time must be between 0 and 1410
solver.add(start_time >= 0)
solver.add(start_time <= 1410)

# Robert wants to avoid Monday, so start_time >= 480 (Tuesday)
solver.add(start_time >= 480)

# Tuesday (480 <= start_time < 960)
# Robert's blocked intervals on Tuesday
solver.add(z3.Or(start_time + 30 <= 570, start_time >= 600))  # 10:30-11:00
solver.add(z3.Or(start_time + 30 <= 840, start_time >= 870))  # 15:00-15:30

# Ralph's blocked intervals on Tuesday
solver.add(z3.Or(start_time + 30 <= 480, start_time >= 510))  # 9:00-9:30
solver.add(z3.Or(start_time + 30 <= 540, start_time >= 570))  # 10:00-10:30
solver.add(z3.Or(start_time + 30 <= 600, start_time >= 630))  # 11:00-11:30
solver.add(z3.Or(start_time + 30 <= 660, start_time >= 720))  # 12:00-13:00
solver.add(z3.Or(start_time + 30 <= 780, start_time >= 870))  # 14:00-15:30
solver.add(z3.Or(start_time + 30 <= 900, start_time >= 960))  # 16:00-17:00

# Wednesday (960 <= start_time < 1440)
# Robert's blocked intervals on Wednesday
solver.add(z3.Or(start_time + 30 <= 1020, start_time >= 1080))  # 10:00-11:00
solver.add(z3.Or(start_time + 30 <= 1110, start_time >= 1140))  # 11:30-12:00
solver.add(z3.Or(start_time + 30 <= 1170, start_time >= 1200))  # 12:30-13:00
solver.add(z3.Or(start_time + 30 <= 1230, start_time >= 1260))  # 13:30-14:00
solver.add(z3.Or(start_time + 30 <= 1320, start_time >= 1350))  # 15:00-15:30
solver.add(z3.Or(start_time + 30 <= 1380, start_time >= 1410))  # 16:00-16:30

# Ralph's blocked intervals on Wednesday
solver.add(z3.Or(start_time + 30 <= 1050, start_time >= 1080))  # 10:30-11:00
solver.add(z3.Or(start_time + 30 <= 1080, start_time >= 1110))  # 11:30-12:00
solver.add(z3.Or(start_time + 30 <= 1320, start_time >= 1380))  # 13:00-14:30
solver.add(z3.Or(start_time + 30 <= 1410, start_time >= 1440))  # 16:30-17:00

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Determine day
    if 480 <= time_minutes < 960:
        day = "Tuesday"
        offset = time_minutes - 480
    elif 960 <= time_minutes < 1440:
        day = "Wednesday"
        offset = time_minutes - 960
    else:
        day = "Unknown"
        offset = 0
    
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