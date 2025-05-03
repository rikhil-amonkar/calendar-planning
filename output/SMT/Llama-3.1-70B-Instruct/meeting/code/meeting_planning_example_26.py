from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Richmond District
end_time = Int('end_time')  # End time at Presidio
travel_time_richmond_to_presidio = 7  # Travel time from Richmond to Presidio
travel_time_presidio_to_richmond = 7  # Travel time from Presidio to Richmond
min_meeting_time = 105  # Minimum meeting time with Sarah

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Richmond District is 9:00 AM
    start_time + travel_time_richmond_to_presidio >= 13 * 60 + 15,  # Arrive at Presidio after 1:15 PM
    end_time >= 13 * 60 + 15,  # Meet Sarah after 1:15 PM
    end_time <= 15 * 60 + 15,  # Meet Sarah before 3:15 PM
    end_time - (start_time + travel_time_richmond_to_presidio) >= min_meeting_time,  # Meet Sarah for at least 105 minutes
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
    print(f"Optimal schedule: Meet Sarah at {13} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")