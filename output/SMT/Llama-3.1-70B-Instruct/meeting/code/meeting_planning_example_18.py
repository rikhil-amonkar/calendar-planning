from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Marina District
end_time = Int('end_time')  # End time at Richmond District
travel_time_marina_to_richmond = 11  # Travel time from Marina to Richmond
travel_time_richmond_to_marina = 9  # Travel time from Richmond to Marina
min_meeting_time = 75  # Minimum meeting time with Betty

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Marina District is 9:00 AM
    start_time + travel_time_marina_to_richmond >= 20 * 60 + 30,  # Arrive at Richmond after 8:30 PM
    end_time >= 20 * 60 + 30,  # Meet Betty after 8:30 PM
    end_time <= 22 * 60,  # Meet Betty before 10:00 PM
    end_time - (start_time + travel_time_marina_to_richmond) >= min_meeting_time,  # Meet Betty for at least 75 minutes
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
    print(f"Optimal schedule: Meet Betty at {20} hours and {30} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")