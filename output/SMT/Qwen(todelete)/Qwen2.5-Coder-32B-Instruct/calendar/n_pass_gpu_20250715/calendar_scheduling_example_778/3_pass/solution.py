from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
hour = Int('hour')  # Hour of the day in 24-hour format
minute = Int('minute')  # Minute of the hour (0 or 30)

# Define the constraints
constraints = []

# Day constraint: must be Monday, Tuesday, or Wednesday
constraints.append(day >= 0)
constraints.append(day <= 2)

# Hour and minute constraints: must be between 9:00 and 16:30
constraints.append(hour >= 9)
constraints.append(hour <= 16)
constraints.append(Or(minute == 0, minute == 30))

# Meeting duration is 30 minutes, so we need to check both hour:minute and hour:minute+30
# Susan's schedule
constraints.append(Or(day != 0, Or(hour < 12, Or(hour == 12, minute < 30))))
constraints.append(Or(day != 0, Or(hour < 13, Or(hour == 13, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 11, Or(hour == 11, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 9, Or(hour == 9, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 14, Or(hour == 14, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 15, Or(hour == 15, minute < 30))))

# Sandra's schedule
constraints.append(Or(day != 0, Or(hour < 9, Or(hour == 9, minute < 30))))
constraints.append(Or(day != 0, Or(hour < 13, Or(hour == 13, minute < 30))))
constraints.append(Or(day != 0, Or(hour < 14, Or(hour == 14, minute < 30))))
constraints.append(Or(day != 0, Or(hour < 16, Or(hour == 16, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 9, Or(hour == 9, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 9, Or(hour == 9, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 10, Or(hour == 10, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 12, Or(hour == 12, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 12, Or(hour == 12, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 13, Or(hour == 13, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 14, Or(hour == 14, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 14, Or(hour == 14, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 16, Or(hour == 16, minute < 30))))
constraints.append(Or(day != 1, Or(hour < 16, Or(hour == 16, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 9, Or(hour == 9, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 11, Or(hour == 11, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 12, Or(hour == 12, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 12, Or(hour == 12, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 13, Or(hour == 13, minute < 30))))
constraints.append(Or(day != 2, Or(hour < 17, Or(hour == 17, minute < 30))))

# Susan does not want to meet on Tuesday
constraints.append(day != 1)

# Sandra cannot meet on Monday after 16:00
constraints.append(Or(day != 0, Or(hour < 16, Or(hour == 16, minute < 30))))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    hour_value = model[hour].as_long()
    minute_value = model[minute].as_long()
    day_str = ["Monday", "Tuesday", "Wednesday"][day_value]
    start_time = f"{hour_value:02}:{minute_value:02}"
    end_time = f"{hour_value:02}:{(minute_value + 30) % 60:02}"
    if minute_value + 30 == 60:
        end_time = f"{hour_value + 1:02}:00"
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")