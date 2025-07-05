from z3 import *

# Define the variables
day = "Monday"
start_time = Int('start_time')
end_time = Int('end_time')
meeting_duration = 60  # 1 hour meeting

# Define the constraints
constraints = []

# Anthony's constraints
constraints.append(start_time < 930) | (start_time >= 1000)
constraints.append(start_time < 1200) | (start_time >= 1300)
constraints.append(start_time < 1600) | (start_time >= 1630)

# Pamela's constraints
constraints.append(start_time < 930) | (start_time >= 1000)
constraints.append(start_time < 1430)  # Pamela does not want to meet after 14:30
constraints.append(start_time < 1630) | (start_time >= 1700)

# Zachary's constraints
constraints.append(start_time < 900) | (start_time >= 1130)
constraints.append(start_time < 1200) | (start_time >= 1230)
constraints.append(start_time < 1300) | (start_time >= 1330)
constraints.append(start_time < 1430) | (start_time >= 1500)
constraints.append(start_time < 1600) | (start_time >= 1700)

# Meeting duration constraint
constraints.append(end_time == start_time + meeting_duration)

# Work hours constraint
constraints.append(start_time >= 900)
constraints.append(end_time <= 1700)

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    start_time_value = model[start_time].as_long()
    end_time_value = model[end_time].as_long()
    
    # Format the output
    start_time_str = f"{start_time_value // 100:02}:{start_time_value % 100:02}"
    end_time_str = f"{end_time_value // 100:02}:{end_time_value % 100:02}"
    
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_time_str} (24-hour format)")
    print(f"End Time: {end_time_str} (24-hour format)")
else:
    print("No solution found")