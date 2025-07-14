from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for the time you start meeting Barbara
start_meeting_barbara = Int('start_meeting_barbara')

# Constraints
# You arrive at Russian Hill at 9:00AM, which we can consider as time 0
# Convert all times to minutes since 9:00AM
# Barbara is available from 1:15PM to 6:15PM
barbara_start = 255  # 1:15PM in minutes since 9:00AM
barbara_end = 495    # 6:15PM in minutes since 9:00AM

# Constraint: You must meet Barbara for at least 45 minutes
solver.add(start_meeting_barbara + 45 <= barbara_end)

# Constraint: You must start meeting Barbara when she is available
solver.add(start_meeting_barbara >= barbara_start)

# Objective: Maximize the time spent meeting Barbara
# Since we are only constrained by the minimum time, we just need to ensure the constraints are met

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time = model[start_meeting_barbara].as_long()
    end_time = start_time + 45
    
    # Convert back to hours and minutes for readability
    start_hour = 9 + start_time // 60
    start_minute = start_time % 60
    end_hour = 9 + end_time // 60
    end_minute = end_time % 60
    
    print(f"SOLUTION: You should start meeting Barbara at {start_hour}:{start_minute:02d} and end at {end_hour}:{end_minute:02d}.")
else:
    print("SOLUTION: It is not possible to meet Barbara under the given constraints.")