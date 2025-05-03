from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Nob Hill
end_time = Int('end_time')  # End time at The Castro
travel_time_nob_hill_to_castro = 17  # Travel time from Nob Hill to The Castro
travel_time_castro_to_nob_hill = 16  # Travel time from The Castro to Nob Hill
min_meeting_time = 75  # Minimum meeting time with William

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Nob Hill is 9:00 AM
    start_time + travel_time_nob_hill_to_castro >= 12 * 60 + 15,  # Arrive at The Castro after 12:15 PM
    end_time >= 12 * 60 + 15,  # Meet William after 12:15 PM
    end_time <= 22 * 60,  # Meet William before 10:00 PM
    end_time - (start_time + travel_time_nob_hill_to_castro) >= min_meeting_time,  # Meet William for at least 75 minutes
]

# Define the objective function
obj = end_time - start_time  # Minimize the total time spent

# Create the Z3 solver
solver = Optimize()
for constraint in constraints:
    solver.add(constraint)

# Define the objective function
solver.minimize(obj)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time_value = model[start_time].as_long() / 60
    end_time_value = model[end_time].as_long() / 60
    print(f"Optimal schedule: Meet William at {12} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")