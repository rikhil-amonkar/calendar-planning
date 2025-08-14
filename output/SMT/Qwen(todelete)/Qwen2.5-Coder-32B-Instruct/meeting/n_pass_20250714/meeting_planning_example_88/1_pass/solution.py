from z3 import *

# Define the solver
solver = Solver()

# Define the time variables for the visit to Golden Gate Park
start_time_joshua_meeting = Int('start_time_joshua_meeting')

# Constraints
# You arrive at Sunset District at 9:00 AM, which is 540 minutes after midnight
arrival_time = 540

# Joshua is available from 8:45 PM to 9:45 PM, which is 1245 to 1305 minutes after midnight
joshua_start = 1245
joshua_end = 1305

# You need to meet Joshua for at least 15 minutes
min_meeting_duration = 15

# Constraint: Meeting with Joshua must start within his availability window
solver.add(start_time_joshua_meeting >= joshua_start)
solver.add(start_time_joshua_meeting + min_meeting_duration <= joshua_end)

# Objective: Maximize the number of friends met. Since no other friends are specified,
# we just need to ensure the meeting with Joshua happens as per the constraints.

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time = model.evaluate(start_time_joshua_meeting).as_long()
    print(f"SOLUTION: Meet Joshua starting at {start_time} minutes after midnight.")
    print(f"Meeting duration: {min_meeting_duration} minutes")
else:
    print("SOLUTION: No feasible schedule found to meet Joshua for at least 15 minutes.")