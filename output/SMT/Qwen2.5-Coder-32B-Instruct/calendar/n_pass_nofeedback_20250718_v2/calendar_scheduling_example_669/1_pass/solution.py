from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the constraints
constraints = [
    # Day constraints
    Or(day == 0, day == 1),
    
    # Work hours constraints
    And(start_hour >= 9, start_hour < 17),
    Or(start_minute == 0, start_minute == 30),
    
    # Jean's busy times
    Not(And(day == 1, start_hour == 11, start_minute == 30)),  # Tuesday 11:30-12:00
    Not(And(day == 1, start_hour == 16, start_minute == 0)),   # Tuesday 16:00-16:30
    
    # Doris's busy times
    Not(And(day == 0, start_hour == 9, start_minute == 0)),    # Monday 9:00-11:30
    Not(And(day == 0, start_hour == 11, start_minute == 30)),
    Not(And(day == 0, start_hour == 12, start_minute == 0)),    # Monday 12:00-12:30
    Not(And(day == 0, start_hour == 12, start_minute == 30)),
    Not(And(day == 0, start_hour == 13, start_minute == 30)),    # Monday 13:30-16:00
    Not(And(day == 0, start_hour == 14, start_minute == 0)),
    Not(And(day == 0, start_hour == 14, start_minute == 30)),
    Not(And(day == 0, start_hour == 15, start_minute == 0)),
    Not(And(day == 0, start_hour == 15, start_minute == 30)),
    Not(And(day == 0, start_hour == 16, start_minute == 0)),
    Not(And(day == 0, start_hour == 16, start_minute == 30)),
    Not(And(day == 0, start_hour == 17, start_minute == 0)),
    Not(And(day == 1, start_hour >= 9, start_hour < 17)),        # Tuesday 9:00-17:00
    
    # Doris's preference
    Or(day == 0, And(day == 0, start_hour < 14))  # Prefer not to meet on Monday after 14:00
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    start_minute_value = model[start_minute].as_long()
    
    # Convert day to string
    day_str = "Monday" if day_value == 0 else "Tuesday"
    
    # Format the start and end times
    start_time_str = f"{start_hour_value:02}:{start_minute_value:02}"
    end_time_str = f"{start_hour_value:02}:{start_minute_value + 30:02}" if start_minute_value == 0 else f"{start_hour_value + 1:02}:00"
    
    # Print the solution
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")