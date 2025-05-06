import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Work hours on Thursday: 1440 to 1890 minutes since Monday 9:00 AM
solver.add(start_time >= 1440)
solver.add(start_time <= 1890)

# Ruth's blocked intervals on Thursday
# 9:00-11:00 (1440-1560)
solver.add(z3.Or(start_time + 30 <= 1440, start_time >= 1560))
# 11:30-14:30 (1590-1770)
solver.add(z3.Or(start_time + 30 <= 1590, start_time >= 1770))
# 15:00-17:00 (1800-1920)
solver.add(z3.Or(start_time + 30 <= 1800, start_time >= 1920))

# Julie's preference: avoid before 11:30 AM on Thursday (1590)
solver.add(start_time >= 1590)

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    thursday_minutes = time_minutes - 1440
    start_hour = 9 + thursday_minutes // 60
    start_min = thursday_minutes % 60
    end_hour = start_hour
    end_min = start_min + 30
    if end_min == 60:
        end_hour += 1
        end_min = 0
    print(f"Start: Thursday {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")