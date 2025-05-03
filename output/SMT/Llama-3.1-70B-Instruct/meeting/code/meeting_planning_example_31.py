from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Nob Hill
end_time = Int('end_time')  # End time at Alamo Square
travel_time_nob_hill_to_alamo_square = 11  # Travel time from Nob Hill to Alamo Square
travel_time_alamo_square_to_nob_hill = 11  # Travel time from Alamo Square to Nob Hill
min_meeting_time = 15  # Minimum meeting time with Anthony

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Nob Hill is 9:00 AM
    start_time + travel_time_nob_hill_to_alamo_square >= 7 * 60 + 15,  # Arrive at Alamo Square after 7:15 AM
    end_time >= 7 * 60 + 15,  # Meet Anthony after 7:15 AM
    end_time <= 13 * 60,  # Meet Anthony before 1:00 PM
    end_time - (start_time + travel_time_nob_hill_to_alamo_square) >= min_meeting_time,  # Meet Anthony for at least 15 minutes
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
    print(f"Optimal schedule: Meet Anthony at {7} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")