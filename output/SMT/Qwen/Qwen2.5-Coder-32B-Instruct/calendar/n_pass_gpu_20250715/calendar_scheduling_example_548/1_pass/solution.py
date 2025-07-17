from z3 import *

# Define the variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
constraints = []

# The meeting must be on Monday
constraints.append(day == "Monday")

# Meeting duration is 30 minutes
constraints.append(end_time == start_time + 30)

# Work hours are from 9:00 to 17:00
constraints.append(start_time >= 9 * 60)  # 9:00 in minutes
constraints.append(end_time <= 17 * 60)   # 17:00 in minutes

# Judy is free the entire day, so no additional constraints for her

# Nicole's busy times are 9:00 to 10:00 and 10:30 to 16:30
# Convert these times to minutes
nicole_busy_times = [(9 * 60, 10 * 60), (10 * 60 + 30, 16 * 60 + 30)]

# Add constraints to ensure the meeting does not overlap with Nicole's busy times
for busy_start, busy_end in nicole_busy_times:
    constraints.append(Or(end_time <= busy_start, start_time >= busy_end))

# Nicole prefers not to meet before 16:00
constraints.append(start_time >= 16 * 60)  # 16:00 in minutes

# Create a solver instance and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    
    print("SOLUTION:")
    print(f"Day: {model[day]}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")