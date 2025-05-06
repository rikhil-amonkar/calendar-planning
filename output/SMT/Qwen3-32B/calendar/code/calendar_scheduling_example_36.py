import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 1 hour long, work hours from 9:00 AM to 5:00 PM (0 to 480 minutes)
# Start time must be between 0 and 420 (since 420 + 60 = 480)
solver.add(start_time >= 0)
solver.add(start_time <= 420)

# Denise's preference: end by 12:30 PM (210 minutes)
solver.add(start_time + 60 <= 210)

# Ryan's blocked intervals
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 60 <= 0, start_time >= 30))
# 12:30-13:00 (210-240)
# Since meeting must end by 210, this is automatically satisfied

# Denise's blocked intervals
# 9:30-10:30 (30-90)
solver.add(z3.Or(start_time + 60 <= 30, start_time >= 90))
# 12:00-13:00 (180-240) - already covered by Denise's end time constraint
# 14:30-16:30 (330-450) - not relevant due to end time constraint

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Convert to 24-hour format
    start_hour = 9 + (time_minutes // 60)
    start_min = time_minutes % 60
    end_hour = start_hour
    end_min = start_min + 60
    if end_min == 60:
        end_hour += 1
        end_min = 0
    
    print(f"Start: {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")