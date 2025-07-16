from z3 import *

# Define the variables for the meeting start time in minutes from 9:00
meeting_start = Int('meeting_start')

# Define the constraints
constraints = [
    # Meeting must be between 9:00 and 17:00
    meeting_start >= 0,          # 9:00 in minutes from 9:00
    meeting_start + 30 <= 480,   # 17:00 in minutes from 9:00
    
    # Juan's availability
    Or(meeting_start >= 90, meeting_start + 30 <= 330),  # 10:30 to 15:30
    meeting_start + 30 <= 360,                         # 16:00
    
    # Marilyn's availability
    Or(meeting_start >= 120, meeting_start + 30 <= 135), # 11:00 to 11:30
    Or(meeting_start >= 210, meeting_start + 30 <= 240), # 12:30 to 13:00
    
    # Ronald's availability
    Or(meeting_start >= 90, meeting_start + 30 <= 330),  # 10:30 to 12:00
    Or(meeting_start >= 360, meeting_start + 30 <= 390), # 12:30 to 13:00
    Or(meeting_start >= 420, meeting_start + 30 <= 450), # 13:30 to 14:00
    meeting_start + 30 <= 420                          # 14:00 to 16:30
]

# Create a solver instance
solver = Solver()

# Add the constraints to the solver
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[meeting_start].as_long()
    start_hour = 9 + start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = 9 + (start_time_minutes + 30) // 60
    end_minute = (start_time_minutes + 30) % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")