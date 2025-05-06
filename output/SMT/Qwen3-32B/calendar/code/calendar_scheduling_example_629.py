import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Work hours on Tuesday (480 to 960 minutes since Monday 9:00 AM)
solver.add(start_time >= 480)
solver.add(start_time <= 960)

# Margaret's preference: after 14:30 (810 minutes since Monday 9:00 AM)
solver.add(start_time >= 810)

# Meeting must end by 17:00 (960 minutes)
solver.add(start_time + 30 <= 960)

# Alexis's blocked interval on Tuesday: 14:00-16:30 (780 to 930 minutes since Monday 9:00 AM)
solver.add(z3.Or(start_time + 30 <= 780, start_time >= 930))

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