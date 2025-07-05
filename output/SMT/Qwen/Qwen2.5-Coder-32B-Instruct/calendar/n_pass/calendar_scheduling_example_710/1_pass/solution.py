from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes since 9:00

# Define the constants for the days
MONDAY = 0
TUESDAY = 1
WEDNESDAY = 2

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
constraints = [
    # Day constraints
    Or(day == MONDAY, day == TUESDAY),  # Cheryl cannot meet on Wednesday
    
    # Cheryl's availability
    Or(
        And(day == MONDAY, Or(start_time < 540, And(start_time >= 570, start_time + meeting_duration <= 780))),
        And(day == TUESDAY, Or(start_time < 900, start_time + meeting_duration <= 930)),
        And(day == WEDNESDAY, False)  # Cheryl cannot meet on Wednesday
    ),
    
    # Kyle's availability
    Or(
        And(day == MONDAY, False),  # Kyle is busy all day on Monday
        And(day == TUESDAY, Or(start_time < 570, start_time + meeting_duration <= 1020)),
        And(day == WEDNESDAY, Or(start_time < 540, And(start_time >= 780, start_time + meeting_duration <= 810),
                                 And(start_time >= 810, start_time + meeting_duration <= 840),
                                 And(start_time >= 870, start_time + meeting_duration <= 885)))
    ),
    
    # Meeting must be within work hours (9:00 to 17:00)
    And(start_time >= 0, start_time + meeting_duration <= 480)
]

# Create the solver
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    # Convert the day number to the actual day name
    if meeting_day == MONDAY:
        day_name = "Monday"
    elif meeting_day == TUESDAY:
        day_name = "Tuesday"
    else:
        day_name = "Wednesday"
    
    # Convert start and end times from minutes since 9:00 to HH:MM format
    start_hour = 9 + meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = 9 + meeting_end_time // 60
    end_minute = meeting_end_time % 60
    
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")