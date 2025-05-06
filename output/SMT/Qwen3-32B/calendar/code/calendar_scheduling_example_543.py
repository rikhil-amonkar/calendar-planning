import z3

# Initialize the Z3 solver
solver = z3.Solver()

# Define the start time variable in minutes after 9:00 AM
start_time = z3.Int('start_time')

# Work hours are from 9:00 AM (0 minutes) to 5:00 PM (480 minutes)
# The meeting is 1 hour long, so start_time must be between 0 and 420
solver.add(start_time >= 0)
solver.add(start_time <= 420)

# James's busy intervals (in minutes after 9:00 AM)
# 11:30-12:00 (150-180)
solver.add(z3.Or(start_time + 60 <= 150, start_time >= 180))
# 14:30-15:00 (330-390)
solver.add(z3.Or(start_time + 60 <= 330, start_time >= 390))

# John's busy intervals (in minutes after 9:00 AM)
# 9:30-11:00 (30-120)
solver.add(z3.Or(start_time + 60 <= 30, start_time >= 120))
# 11:30-12:00 (150-180)
solver.add(z3.Or(start_time + 60 <= 150, start_time >= 180))
# 12:30-13:30 (150-210)
solver.add(z3.Or(start_time + 60 <= 150, start_time >= 210))
# 14:30-16:30 (330-450)
solver.add(z3.Or(start_time + 60 <= 330, start_time >= 450))

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