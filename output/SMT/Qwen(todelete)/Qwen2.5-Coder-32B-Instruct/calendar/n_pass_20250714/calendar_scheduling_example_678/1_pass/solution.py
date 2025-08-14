from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 9:00

# Define constants for the time range
nine_am = 0  # 9:00 in minutes from 9:00
five_pm = 480  # 17:00 in minutes from 9:00
one_hour = 60  # one hour in minutes

# Define the constraints
constraints = [
    Or(day == 0, day == 1),  # day must be either Monday or Tuesday
    nine_am <= start_time,  # start time must be after or at 9:00
    start_time + one_hour <= five_pm,  # meeting must end before or at 17:00
    
    # Russell's busy times
    Or(start_time >= 60, start_time + one_hour <= 10*60),  # not 10:30 to 11:00 on Monday
    Or(day == 0, start_time >= 8*60),  # not before 13:30 on Tuesday
    
    # Alexander's busy times on Monday
    Or(start_time >= 150, start_time + one_hour <= 12*60),  # not 9:00 to 11:30
    Or(start_time >= 240, start_time + one_hour <= 15*60),  # not 12:00 to 14:30
    Or(start_time >= 300, start_time + one_hour <= 17*60),  # not 15:00 to 17:00
    
    # Alexander's busy times on Tuesday
    Or(day == 1, start_time >= 60),  # not 9:00 to 10:00
    Or(day == 1, start_time >= 8*60, start_time + one_hour <= 13*60),  # not 13:00 to 14:00
    Or(day == 1, start_time >= 300, start_time + one_hour <= 303),  # not 15:00 to 15:30
    Or(day == 1, start_time >= 360, start_time + one_hour <= 378)  # not 16:00 to 16:30
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + one_hour
    
    # Convert meeting start and end times to HH:MM format
    start_hour = 9 + meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = 9 + meeting_end_time // 60
    end_minute = meeting_end_time % 60
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")