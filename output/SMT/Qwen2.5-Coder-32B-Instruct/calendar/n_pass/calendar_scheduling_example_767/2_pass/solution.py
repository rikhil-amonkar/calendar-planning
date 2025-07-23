from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = [
    # Day constraints
    Or(day == 0, day == 1, day == 2),
    
    # Time constraints (9:00 to 17:00 in minutes)
    start_time >= 0,  # 9:00
    start_time + 60 <= 480,  # 17:00 (480 minutes from 9:00)
    
    # Martha's constraints
    Or(start_time + 60 <= 90, start_time >= 1020),  # Monday 16:00 to 17:00
    Or(start_time + 60 <= 930, start_time >= 990),  # Tuesday 15:00 to 15:30
    Or(start_time + 60 <= 600, start_time >= 660),  # Wednesday 10:00 to 11:00
    Or(start_time + 60 <= 870, start_time >= 930),  # Wednesday 14:00 to 14:30
    
    # Beverly's constraints
    Or(start_time + 60 <= 270, start_time >= 840),  # Monday 9:00 to 13:30
    Or(start_time + 60 <= 270, start_time >= 1020),  # Monday 14:00 to 17:00
    Or(start_time + 60 <= 570, start_time >= 990),  # Tuesday 9:00 to 17:00
    Or(start_time + 60 <= 570, start_time >= 930),  # Wednesday 9:30 to 15:30
    Or(start_time + 60 <= 1020, start_time >= 1050)  # Wednesday 16:30 to 17:00
]

# Correct the constraints for Monday, Tuesday, and Wednesday
# Monday constraints
constraints.append(Or(start_time + 60 <= 90, start_time >= 840))  # Monday 9:00 to 13:30 and 14:00 to 17:00
constraints.append(Or(start_time + 60 <= 90, start_time >= 1020))  # Monday 16:00 to 17:00

# Tuesday constraints
constraints.append(Or(start_time + 60 <= 930, start_time >= 990))  # Tuesday 15:00 to 15:30

# Wednesday constraints
constraints.append(Or(start_time + 60 <= 600, start_time >= 660))  # Wednesday 10:00 to 11:00
constraints.append(Or(start_time + 60 <= 870, start_time >= 930))  # Wednesday 14:00 to 14:30
constraints.append(Or(start_time + 60 <= 570, start_time >= 930))  # Wednesday 9:30 to 15:30
constraints.append(Or(start_time + 60 <= 1020, start_time >= 1050))  # Wednesday 16:30 to 17:00

# Create a solver instance
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    
    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_hour = 9 + start_time_value // 60
    start_minute = start_time_value % 60
    end_hour = start_hour + 1
    end_minute = start_minute
    
    # Format the output
    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")