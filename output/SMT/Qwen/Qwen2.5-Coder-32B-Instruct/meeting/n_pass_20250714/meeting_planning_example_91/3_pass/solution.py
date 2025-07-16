from z3 import *

# Define the solver
solver = Solver()

# Define the time variable in minutes since 9:00 AM
start_time_richmond_district = Int('start_time_richmond_district')

# Constraints
# Daniel is available from 7:00 PM to 8:15 PM
# 7:00 PM is 600 minutes after 9:00 AM
# 8:15 PM is 615 minutes after 9:00 AM
daniel_start_time = 600
daniel_end_time = 615

# You need to meet Daniel for a minimum of 75 minutes
min_meeting_time_with_daniel = 75

# Constraint to meet Daniel for at least 75 minutes
solver.add(start_time_richmond_district + min_meeting_time_with_daniel <= daniel_end_time)
solver.add(start_time_richmond_district >= daniel_start_time)

# Check if the problem is solvable and get the model
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    print(f"Start time at Richmond District: {model[start_time_richmond_district]} minutes after 9:00 AM")
else:
    print("No solution found.")