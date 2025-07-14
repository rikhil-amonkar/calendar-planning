from z3 import *

# Define the variables for the day and time
day = Int('day')
start_time = Int('start_time')

# Define the constants for days and time intervals
MONDAY, TUESDAY, WEDNESDAY, THURSDAY = 1, 2, 3, 4

# Define the constraints
constraints = [
    # Day should be one of the specified days
    Or(day == MONDAY, day == TUESDAY, day == WEDNESDAY, day == THURSDAY),
    
    # Start time should be within work hours (9:00 to 17:00) and aligned with 30-minute intervals
    And(start_time >= 540, start_time <= 1020),  # 9:00 to 17:00 in minutes since midnight
    start_time % 30 == 0,
    
    # Meeting duration is 30 minutes
    Int('end_time') == start_time + 30,
    
    # Cheryl's schedule is always open
    
    # James' schedule constraints
    Or(
        # Monday
        Not(And(day == MONDAY, start_time >= 540, start_time < 570)),  # 9:00 to 9:30
        Not(And(day == MONDAY, start_time >= 630, start_time < 660)),  # 10:30 to 11:00
        Not(And(day == MONDAY, start_time >= 750, start_time < 780)),  # 12:30 to 13:00
        Not(And(day == MONDAY, start_time >= 870, start_time < 900)),  # 14:30 to 15:00
        Not(And(day == MONDAY, start_time >= 990, start_time < 1020)), # 16:30 to 17:00
        
        # Tuesday
        Not(And(day == TUESDAY, start_time >= 540, start_time < 660)),  # 9:00 to 11:00
        Not(And(day == TUESDAY, start_time >= 690, start_time < 720)),  # 11:30 to 12:00
        Not(And(day == TUESDAY, start_time >= 750, start_time < 930)),  # 12:30 to 15:30
        Not(And(day == TUESDAY, start_time >= 960, start_time < 1020)), # 16:00 to 17:00
        
        # Wednesday
        Not(And(day == WEDNESDAY, start_time >= 600, start_time < 660)), # 10:00 to 11:00
        Not(And(day == WEDNESDAY, start_time >= 720, start_time < 780)), # 12:00 to 13:00
        Not(And(day == WEDNESDAY, start_time >= 810, start_time < 960)), # 13:30 to 16:00
        
        # Thursday
        Not(And(day == THURSDAY, start_time >= 570, start_time < 690)),  # 9:30 to 11:30
        Not(And(day == THURSDAY, start_time >= 720, start_time < 750)),  # 12:00 to 12:30
        Not(And(day == THURSDAY, start_time >= 780, start_time < 810)),  # 13:00 to 13:30
        Not(And(day == THURSDAY, start_time >= 840, start_time < 870)),  # 14:00 to 14:30
        Not(And(day == THURSDAY, start_time >= 990, start_time < 1020))  # 16:30 to 17:00
    ),
    
    # Cheryl would rather not meet on Wednesday or Thursday
    Or(day == MONDAY, day == TUESDAY)
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 30
    
    # Convert day number to day name
    day_name = {MONDAY: "Monday", TUESDAY: "Tuesday", WEDNESDAY: "Wednesday", THURSDAY: "Thursday"}[day_value]
    
    # Convert time from minutes since midnight to HH:MM format
    start_hour = start_time_value // 60
    start_minute = start_time_value % 60
    end_hour = end_time_value // 60
    end_minute = end_time_value % 60
    
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")