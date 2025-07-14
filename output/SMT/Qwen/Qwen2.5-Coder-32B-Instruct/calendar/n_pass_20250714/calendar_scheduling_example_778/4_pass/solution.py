from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = [
    # Day must be one of Monday, Tuesday, or Wednesday
    Or(day == 0, day == 1, day == 2),
    
    # Meeting duration is 30 minutes
    start_time >= 0,
    start_time <= 480 - 30,  # 480 minutes from 9:00 to 17:00, minus 30 minutes
    
    # Susan's availability
    Or(
        And(day == 0, Or(start_time < 75, start_time >= 85, start_time < 95, start_time >= 105)),  # Monday
        And(day == 1, False),  # Tuesday (not allowed)
        And(day == 2, Or(start_time < 15, start_time >= 25, start_time < 85, start_time >= 95, start_time < 105, start_time >= 115))  # Wednesday
    ),
    
    # Sandra's availability
    Or(
        And(day == 0, Or(start_time < 240, start_time >= 300, start_time < 360, start_time >= 420)),  # Monday
        And(day == 1, Or(start_time < 55, start_time >= 65, start_time < 85, start_time >= 95, start_time < 105, start_time >= 115)),  # Tuesday
        And(day == 2, Or(start_time < 120, start_time >= 135, start_time < 150, start_time >= 180))  # Wednesday
    ),
    
    # Susan's preference: not on Tuesday
    day != 1,
    
    # Sandra's constraint: not on Monday after 16:00
    Or(day != 0, start_time < 360)
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    
    # Convert day number to name
    day_name = ["Monday", "Tuesday", "Wednesday"][day_value]
    
    # Convert start time from minutes to HH:MM format
    start_hour = 9 + start_time_value // 60
    start_minute = start_time_value % 60
    start_time_str = f"{start_hour:02}:{start_minute:02}"
    
    # Calculate end time
    end_time_value = start_time_value + 30
    end_hour = 9 + end_time_value // 60
    end_minute = end_time_value % 60
    end_time_str = f"{end_hour:02}:{end_minute:02}"
    
    # Print the solution
    print("SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found")