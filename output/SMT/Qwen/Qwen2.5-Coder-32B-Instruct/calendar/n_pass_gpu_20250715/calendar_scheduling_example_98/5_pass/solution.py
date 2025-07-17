from z3 import *

# Define the variables for the meeting start time in minutes from 9:00
meeting_start = Int('meeting_start')

# Define the constraints
constraints = [
    # Meeting must be between 9:00 and 17:00
    meeting_start >= 0,          # 9:00 in minutes from 9:00
    meeting_start + 30 <= 480,   # 17:00 in minutes from 9:00
    
    # Specific time slot for the meeting
    meeting_start == 135         # 11:30 in minutes from 9:00
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