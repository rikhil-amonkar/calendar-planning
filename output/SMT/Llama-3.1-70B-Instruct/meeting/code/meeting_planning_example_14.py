from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Nob Hill
end_time = Int('end_time')  # End time at Marina District
travel_time_nob_hill_to_marina = 11  # Travel time from Nob Hill to Marina
travel_time_marina_to_nob_hill = 12  # Travel time from Marina to Nob Hill
min_meeting_time = 120  # Minimum meeting time with Mary

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Nob Hill is 9:00 AM
    start_time + travel_time_nob_hill_to_marina >= 20 * 60,  # Arrive at Marina after 8:00 PM
    end_time >= 20 * 60,  # Meet Mary after 8:00 PM
    end_time <= 22 * 60,  # Meet Mary before 10:00 PM
    end_time - (start_time + travel_time_nob_hill_to_marina) >= min_meeting_time,  # Meet Mary for at least 120 minutes
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
    print(f"Optimal schedule: Meet Mary at {20} hours and leave at {end_time_value} hours")
else:
    print("No solution found")