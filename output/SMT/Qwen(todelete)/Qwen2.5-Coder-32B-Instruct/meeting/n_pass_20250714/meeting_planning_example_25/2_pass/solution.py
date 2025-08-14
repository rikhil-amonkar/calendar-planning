from z3 import *

# Define the solver
solver = Solver()

# Define the variables
start_meeting_with_david = Int('start_meeting_with_david')
end_meeting_with_david = Int('end_meeting_with_david')

# Constraints
# You must meet David between 4:00 PM and 9:45 PM (300 to 585 minutes after 9:00 AM)
solver.add(start_meeting_with_david >= 300)
solver.add(end_meeting_with_david <= 585)

# The meeting duration must be at least 105 minutes
solver.add(end_meeting_with_david - start_meeting_with_david >= 105)

# Ensure the meeting starts before it ends
solver.add(start_meeting_with_david < end_meeting_with_david)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    start_time = model[start_meeting_with_david].as_long()
    end_time = model[end_meeting_with_david].as_long()
    print(f"SOLUTION: You can meet David from {start_time} minutes to {end_time} minutes after 9:00 AM.")
else:
    print("SOLUTION: It is not possible to meet David for at least 105 minutes within his availability window.")