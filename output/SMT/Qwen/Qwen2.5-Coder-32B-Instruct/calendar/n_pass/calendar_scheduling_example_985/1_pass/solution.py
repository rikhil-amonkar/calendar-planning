from z3 import *

# Define the days of the week as integers for easier handling
days = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2, 'Thursday': 3, 'Friday': 4}

# Create variables for the day and time of the meeting
meeting_day = Int('meeting_day')
start_time = Int('start_time')

# Define the meeting duration
meeting_duration = 60  # in minutes

# Define the constraints for Diane's schedule
diane_constraints = [
    Or(start_time + meeting_duration <= 12*60, start_time >= 12*60 + 30),  # Monday
    Or(start_time + meeting_duration <= 15*60, start_time >= 15*60 + 30),  # Monday
    Or(start_time + meeting_duration <= 10*60, start_time >= 11*60),      # Tuesday
    Or(start_time + meeting_duration <= 11*60 + 30, start_time >= 12*60),  # Tuesday
    Or(start_time + meeting_duration <= 12*60 + 30, start_time >= 13*60),  # Tuesday
    Or(start_time + meeting_duration <= 16*60, start_time >= 17*60),      # Tuesday
    Or(start_time + meeting_duration <= 9*60 + 30, start_time >= 9*60 + 30), # Wednesday
    Or(start_time + meeting_duration <= 14*60 + 30, start_time >= 15*60),  # Wednesday
    Or(start_time + meeting_duration <= 16*60 + 30, start_time >= 17*60),  # Wednesday
    Or(start_time + meeting_duration <= 15*60 + 30, start_time >= 16*60 + 30), # Thursday
    Or(start_time + meeting_duration <= 9*60 + 30, start_time >= 11*60 + 30), # Friday
    Or(start_time + meeting_duration <= 14*60 + 30, start_time >= 15*60),  # Friday
    Or(start_time + meeting_duration <= 16*60, start_time >= 17*60)        # Friday
]

# Define the constraints for Matthew's schedule
matthew_constraints = [
    Or(start_time + meeting_duration <= 10*60, start_time >= 10*60 + 30),  # Monday
    Or(start_time + meeting_duration <= 9*60, start_time >= 17*60),       # Tuesday
    Or(start_time + meeting_duration <= 9*60, start_time >= 11*60),       # Wednesday
    Or(start_time + meeting_duration <= 12*60, start_time >= 14*60 + 30),  # Wednesday
    Or(start_time + meeting_duration <= 16*60, start_time >= 17*60),       # Wednesday
    Or(start_time + meeting_duration <= 9*60, start_time >= 16*60),       # Thursday
    Or(start_time + meeting_duration <= 9*60, start_time >= 17*60)        # Friday
]

# Matthew's preference: would rather not meet on Wednesday before 12:30
matthew_preference = Or(meeting_day != 2, start_time >= 12*60 + 30)

# General constraints: meeting must be within work hours (9:00 to 17:00) and on a valid day
general_constraints = [
    meeting_day >= 0,
    meeting_day <= 4,
    start_time >= 9*60,
    start_time + meeting_duration <= 17*60
]

# Combine all constraints
constraints = diane_constraints + matthew_constraints + [matthew_preference] + general_constraints

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_of_week = list(days.keys())[model[meeting_day].as_long()]
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = (model[start_time].as_long() + meeting_duration) // 60
    end_minute = (model[start_time].as_long() + meeting_duration) % 60
    print(f"SOLUTION:\nDay: {day_of_week}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")