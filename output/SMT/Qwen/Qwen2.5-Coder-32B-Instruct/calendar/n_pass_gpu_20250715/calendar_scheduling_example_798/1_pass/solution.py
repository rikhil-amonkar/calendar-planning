from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constants for the days
MONDAY = 0
TUESDAY = 1
WEDNESDAY = 2

# Define the meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define the constraints for Nancy's availability
nancy_constraints = [
    Or(day != MONDAY, Or(start_time < 60, start_time >= 630)),  # 10:00 to 10:30
    Or(day != MONDAY, Or(start_time < 750, start_time >= 780)),  # 12:30 to 13:30
    Or(day != MONDAY, Or(start_time < 810, start_time >= 840)),  # 13:30 to 14:00
    Or(day != MONDAY, Or(start_time < 870, start_time >= 900)),  # 14:30 to 15:30
    Or(day != MONDAY, Or(start_time < 960, start_time >= 1080)), # 16:00 to 17:00
    Or(day != TUESDAY, Or(start_time < 30, start_time >= 60)),   # 9:30 to 10:30
    Or(day != TUESDAY, Or(start_time < 660, start_time >= 690)), # 11:00 to 11:30
    Or(day != TUESDAY, Or(start_time < 720, start_time >= 750)), # 12:00 to 12:30
    Or(day != TUESDAY, Or(start_time < 780, start_time >= 810)), # 13:00 to 13:30
    Or(day != TUESDAY, Or(start_time < 930, start_time >= 960)), # 15:30 to 16:00
    Or(day != WEDNESDAY, Or(start_time < 60, start_time >= 750)),# 10:00 to 11:30
    Or(day != WEDNESDAY, Or(start_time < 810, start_time >= 960))# 13:30 to 16:00
]

# Define the constraints for Jose's availability
jose_constraints = [
    Or(day != MONDAY, False),                                  # Busy all day
    Or(day != TUESDAY, False),                                  # Busy all day
    Or(day != WEDNESDAY, Or(start_time < 30, start_time >= 750)),# 9:00 to 9:30, 10:00 to 12:30
    Or(day != WEDNESDAY, Or(start_time < 810, start_time >= 870)),# 13:30 to 14:30
    Or(day != WEDNESDAY, Or(start_time < 900, start_time >= 1080))# 15:00 to 17:00
]

# Define the constraints for the meeting duration and working hours
general_constraints = [
    day >= 0,
    day <= 2,
    start_time >= 0,
    start_time + meeting_duration <= 480  # 16:00 in minutes from 9:00
]

# Create the solver and add the constraints
solver = Solver()
solver.add(nancy_constraints)
solver.add(jose_constraints)
solver.add(general_constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration
    
    # Convert the day value to the corresponding day name
    day_name = ["Monday", "Tuesday", "Wednesday"][day_value]
    
    # Convert the start and end times to HH:MM format
    start_hour = 9 + start_time_value // 60
    start_minute = start_time_value % 60
    end_hour = 9 + end_time_value // 60
    end_minute = end_time_value % 60
    
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")