from z3 import *

# Define variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday
start_time = Int('start_time')  # in minutes since 9:00

# Constants for the days
MONDAY = 1
TUESDAY = 2
WEDNESDAY = 3

# Meeting duration in minutes
meeting_duration = 60

# Define constraints for Martha's availability
martha_unavailable = Or(
    And(day == MONDAY, start_time >= 600, start_time < 720),  # 16:00 to 17:00
    And(day == TUESDAY, start_time >= 540, start_time < 570),  # 15:00 to 15:30
    And(day == WEDNESDAY, start_time >= 0, start_time < 60),   # 10:00 to 11:00
    And(day == WEDNESDAY, start_time >= 300, start_time < 330)  # 14:00 to 14:30
)

# Define constraints for Beverly's availability
beverly_unavailable = Or(
    And(day == MONDAY, start_time >= 0, start_time < 810),  # 9:00 to 13:30
    And(day == MONDAY, start_time >= 840, start_time < 1080),  # 14:00 to 17:00
    And(day == TUESDAY, start_time >= 0, start_time < 1080),  # 9:00 to 17:00
    And(day == WEDNESDAY, start_time >= 180, start_time < 930),  # 9:30 to 15:30
    And(day == WEDNESDAY, start_time >= 990, start_time < 1080)  # 16:30 to 17:00
)

# General constraints for the problem
constraints = [
    Or(day == MONDAY, day == TUESDAY, day == WEDNESDAY),
    start_time >= 0,
    start_time + meeting_duration <= 480  # 9:00 to 17:00 in minutes
]

# Add availability constraints
constraints.append(Not(martha_unavailable))
constraints.append(Not(beverly_unavailable))

# Create solver instance
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    
    # Convert start time from minutes since 9:00 to HH:MM format
    start_hour = 9 + start_time_value // 60
    start_minute = start_time_value % 60
    end_hour = start_hour + meeting_duration // 60
    end_minute = start_minute + meeting_duration % 60
    
    # Adjust end time if it crosses the hour mark
    if end_minute >= 60:
        end_hour += 1
        end_minute -= 60
    
    # Format the day
    if day_value == MONDAY:
        day_str = "Monday"
    elif day_value == TUESDAY:
        day_str = "Tuesday"
    else:
        day_str = "Wednesday"
    
    # Print the solution
    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")