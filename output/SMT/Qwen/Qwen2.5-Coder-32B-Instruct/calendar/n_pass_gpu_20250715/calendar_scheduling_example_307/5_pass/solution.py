from z3 import *

# Define the variables for the meeting start time
start_time = Int('start_time')

# Define the duration of the meeting
meeting_duration = 30  # in minutes

# Define the work hours
work_start = 9 * 60  # 9:00 AM in minutes from 00:00
work_end = 17 * 60   # 5:00 PM in minutes from 00:00

# Define the constraints for each participant
constraints = [
    # Ronald is available the entire day
    And(start_time >= work_start, start_time + meeting_duration <= work_end),
    
    # Stephen is unavailable from 10:00 to 10:30 and 12:00 to 12:30
    Or(start_time + meeting_duration <= 10 * 60, start_time >= 10 * 60 + 30),
    Or(start_time + meeting_duration <= 12 * 60, start_time >= 12 * 60 + 30),
    
    # Brittany is unavailable from 11:00 to 11:30, 13:30 to 14:00, 15:30 to 16:00, 16:30 to 17:00
    Or(start_time + meeting_duration <= 11 * 60, start_time >= 11 * 60 + 30),
    Or(start_time + meeting_duration <= 13 * 60 + 30, start_time >= 14 * 60),
    Or(start_time + meeting_duration <= 15 * 60 + 30, start_time >= 16 * 60),
    Or(start_time + meeting_duration <= 16 * 60 + 30, start_time >= 17 * 60),
    
    # Dorothy is unavailable from 9:00 to 9:30, 10:00 to 10:30, 11:00 to 12:30, 13:00 to 15:00, 15:30 to 17:00
    Or(start_time + meeting_duration <= 9 * 60 + 30, start_time >= 9 * 60 + 30),
    Or(start_time + meeting_duration <= 10 * 60 + 30, start_time >= 10 * 60 + 30),
    Or(start_time + meeting_duration <= 11 * 60, start_time >= 12 * 60 + 30),
    Or(start_time + meeting_duration <= 13 * 60, start_time >= 15 * 60),
    Or(start_time + meeting_duration <= 15 * 60 + 30, start_time >= 17 * 60),
    
    # Rebecca is unavailable from 9:30 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:00 to 17:00
    Or(start_time + meeting_duration <= 9 * 60 + 30, start_time >= 10 * 60 + 30),
    Or(start_time + meeting_duration <= 11 * 60, start_time >= 11 * 60 + 30),
    Or(start_time + meeting_duration <= 12 * 60, start_time >= 12 * 60 + 30),
    Or(start_time + meeting_duration <= 13 * 60, start_time >= 17 * 60),
    
    # Jordan is unavailable from 9:00 to 9:30, 10:00 to 11:00, 11:30 to 12:00, 13:00 to 15:00, 15:30 to 16:30
    Or(start_time + meeting_duration <= 9 * 60 + 30, start_time >= 9 * 60 + 30),
    Or(start_time + meeting_duration <= 10 * 60, start_time >= 11 * 60),
    Or(start_time + meeting_duration <= 11 * 60 + 30, start_time >= 12 * 60),
    Or(start_time + meeting_duration <= 13 * 60, start_time >= 15 * 60),
    Or(start_time + meeting_duration <= 15 * 60 + 30, start_time >= 16 * 60 + 30)
]

# Create a solver instance
solver = Solver()

# Add the constraints to the solver
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_minutes = model[start_time].as_long()
    start_hour = start_minutes // 60
    start_minute = start_minutes % 60
    end_minutes = start_minutes + meeting_duration
    end_hour = end_minutes // 60
    end_minute = end_minutes % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found.")