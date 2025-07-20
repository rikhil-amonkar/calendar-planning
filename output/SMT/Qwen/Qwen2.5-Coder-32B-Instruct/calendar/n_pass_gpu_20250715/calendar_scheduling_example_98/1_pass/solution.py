from z3 import *

# Define the variables for the meeting start time
meeting_start = Int('meeting_start')

# Define the constraints
constraints = [
    # Meeting must be between 9:00 and 17:00
    meeting_start >= 9 * 60,
    meeting_start + 30 <= 17 * 60,
    
    # Juan's availability
    Or(meeting_start >= 10 * 60 + 30, meeting_start + 30 <= 15 * 60 + 30),
    meeting_start + 30 <= 16 * 0,
    
    # Marilyn's availability
    Or(meeting_start >= 11 * 60 + 30, meeting_start + 30 <= 12 * 30),
    Or(meeting_start >= 13 * 60, meeting_start + 30 <= 12 * 30 + 30),
    
    # Ronald's availability
    Or(meeting_start >= 10 * 60 + 30, meeting_start + 30 <= 12 * 0),
    Or(meeting_start >= 12 * 30 + 30, meeting_start + 30 <= 13 * 0),
    Or(meeting_start >= 13 * 30 + 30, meeting_start + 30 <= 14 * 0),
    meeting_start + 30 <= 14 * 60
]

# Create a solver instance
solver = Solver()

# Add the constraints to the solver
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[meeting_start].as_long()
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = (start_time_minutes + 30) // 60
    end_minute = (start_time_minutes + 30) % 60
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")