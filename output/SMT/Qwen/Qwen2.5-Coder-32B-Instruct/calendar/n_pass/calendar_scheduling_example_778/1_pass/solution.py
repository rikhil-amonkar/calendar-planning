from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
hour = Int('hour')  # Hour of the day in 24-hour format

# Define the constraints
constraints = []

# Day constraint: must be Monday, Tuesday, or Wednesday
constraints.append(day >= 0)
constraints.append(day <= 2)

# Hour constraint: must be between 9:00 and 17:00
constraints.append(hour >= 9)
constraints.append(hour < 17)

# Meeting duration is 30 minutes, so we need to check both hour and hour+0.5
# Susan's schedule
constraints.append(Or(day != 0, Or(hour < 12, hour >= 14)))
constraints.append(Or(day != 1, Or(hour < 11, hour >= 12)))
constraints.append(Or(day != 2, Or(hour < 9, hour >= 10)))
constraints.append(Or(day != 2, Or(hour < 14, hour >= 14.5)))
constraints.append(Or(day != 2, Or(hour < 15.5, hour >= 16.5)))

# Sandra's schedule
constraints.append(Or(day != 0, Or(hour < 9, hour >= 13)))
constraints.append(Or(day != 0, Or(hour < 14, hour >= 16)))
constraints.append(Or(day != 1, Or(hour < 9, hour >= 9.5)))
constraints.append(Or(day != 1, Or(hour < 10.5, hour >= 12)))
constraints.append(Or(day != 1, Or(hour < 12.5, hour >= 13.5)))
constraints.append(Or(day != 1, Or(hour < 14, hour >= 14.5)))
constraints.append(Or(day != 1, Or(hour < 16, hour >= 17)))
constraints.append(Or(day != 2, Or(hour < 9, hour >= 11.5)))
constraints.append(Or(day != 2, Or(hour < 12, hour >= 12.5)))
constraints.append(Or(day != 2, Or(hour < 13, hour >= 17)))

# Susan does not want to meet on Tuesday
constraints.append(day != 1)

# Sandra cannot meet on Monday after 16:00
constraints.append(Or(day != 0, hour < 16))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    hour_value = model[hour].as_long()
    day_str = ["Monday", "Tuesday", "Wednesday"][day_value]
    start_time = f"{hour_value:02}:{int((model[hour] - hour_value) * 60):02}"
    end_time = f"{hour_value + 0.5:02}:{int(((model[hour] - hour_value) * 60) + 30):02}"
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")