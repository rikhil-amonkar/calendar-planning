from z3 import *

# Define the variables
day = "Monday"
meeting_start = Int('meeting_start')
meeting_duration = 60  # Meeting duration in minutes

# Define the constraints
constraints = [
    meeting_start >= 9 * 60,  # Start time should be after 9:00
    meeting_start + meeting_duration <= 17 * 60,  # End time should be before 17:00
    
    # James' blocked times
    Or(meeting_start + meeting_duration <= 11 * 60 + 30, meeting_start >= 12 * 60),
    Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 15 * 60),
    
    # John's blocked times
    Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 11 * 60),
    Or(meeting_start + meeting_duration <= 11 * 60 + 30, meeting_start >= 12 * 60),
    Or(meeting_start + meeting_duration <= 12 * 60 + 30, meeting_start >= 13 * 60),
    Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 16 * 60 + 30)
]

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[meeting_start].as_long()
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = (start_time_minutes + meeting_duration) // 60
    end_minute = (start_time_minutes + meeting_duration) % 60
    
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")