from z3 import *

# Define the variables for the meeting day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Constants for the time range
nine_am = 9 * 60
five_pm = 17 * 60
half_hour = 30

# Define the constraints
constraints = [
    # Day should be either Monday or Tuesday
    Or(day == 0, day == 1),
    
    # Meeting should start between 9:00 and 16:30
    start_time >= nine_am,
    start_time + half_hour <= five_pm,
    
    # Jesse's busy times
    Or(start_time + half_hour <= 13 * 60 or start_time >= 14 * 60, day == 1),  # Monday
    Or(start_time + half_hour <= 9 * 60 or start_time >= 9 * 60 + 30, day == 1),  # Tuesday
    Or(start_time + half_hour <= 13 * 60 or start_time >= 13 * 60 + 30, day == 1),  # Tuesday
    Or(start_time + half_hour <= 14 * 60 or start_time >= 15 * 60, day == 1),  # Tuesday
    
    # Lawrence's busy times
    Or(day == 1),  # Lawrence is busy all day Monday
    Or(start_time + half_hour <= 9 * 60 + 30 or start_time >= 10 * 60 + 30, day == 1),  # Tuesday
    Or(start_time + half_hour <= 11 * 60 + 30 or start_time >= 12 * 60 + 30, day == 1),  # Tuesday
    Or(start_time + half_hour <= 13 * 60 or start_time >= 13 * 60 + 30, day == 1),  # Tuesday
    Or(start_time + half_hour <= 14 * 60 + 30 or start_time >= 15 * 60 + 30, day == 1),  # Tuesday
    Or(start_time + half_hour <= 15 * 60 + 30 or start_time >= 16 * 60 + 30, day == 1),  # Tuesday
]

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time = model[start_time].as_long()
    meeting_start_time_str = f"{meeting_start_time // 60:02}:{meeting_start_time % 60:02}"
    meeting_end_time_str = f"{(meeting_start_time + half_hour) // 60:02}:{(meeting_start_time + half_hour) % 60:02}"
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time_str}\nEnd Time: {meeting_end_time_str}")
else:
    print("No solution found")