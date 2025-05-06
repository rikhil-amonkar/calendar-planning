import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Work hours on Tuesday (480 to 960 minutes since Monday 9:00 AM)
# Meeting is 30 minutes, so start_time must be between 480 and 930 (16:30)
solver.add(start_time >= 480)
solver.add(start_time <= 930)

# Jesse's blocked intervals on Tuesday
# 9:00-9:30 (480-510)
solver.add(z3.Or(start_time + 30 <= 480, start_time >= 510))
# 13:00-13:30 (720-750)
solver.add(z3.Or(start_time + 30 <= 720, start_time >= 750))
# 14:00-15:00 (780-840)
solver.add(z3.Or(start_time + 30 <= 780, start_time >= 840))

# Lawrence's blocked intervals on Tuesday
# 9:30-10:30 (510-570)
solver.add(z3.Or(start_time + 30 <= 510, start_time >= 570))
# 11:30-12:30 (690-750)
solver.add(z3.Or(start_time + 30 <= 690, start_time >= 750))
# 13:00-13:30 (720-750)
solver.add(z3.Or(start_time + 30 <= 720, start_time >= 750))
# 14:30-15:00 (810-840)
solver.add(z3.Or(start_time + 30 <= 810, start_time >= 840))
# 15:30-16:30 (870-930)
solver.add(z3.Or(start_time + 30 <= 870, start_time >= 930))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Convert to Tuesday's time
    tuesday_minutes = time_minutes - 480
    start_hour = 9 + (tuesday_minutes // 60)
    start_min = tuesday_minutes % 60
    end_hour = start_hour
    end_min = start_min + 30
    if end_min == 60:
        end_hour += 1
        end_min = 0
    
    print(f"Start: Tuesday {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")