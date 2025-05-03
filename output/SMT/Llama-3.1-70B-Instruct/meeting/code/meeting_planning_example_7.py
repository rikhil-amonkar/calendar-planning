from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Richmond District
end_time = Int('end_time')  # End time at North Beach
travel_time_richmond_to_north_beach = 17  # Travel time from Richmond to North Beach
travel_time_north_beach_to_richmond = 18  # Travel time from North Beach to Richmond
min_meeting_time = 75  # Minimum meeting time with John

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Richmond District is 9:00 AM
    start_time + travel_time_richmond_to_north_beach >= 15 * 60 + 15,  # Arrive at North Beach after 3:15 PM
    end_time >= 15 * 60 + 15,  # Meet John after 3:15 PM
    end_time <= 17 * 60 + 15,  # Meet John before 5:15 PM
    end_time - (start_time + travel_time_richmond_to_north_beach) >= min_meeting_time,  # Meet John for at least 75 minutes
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
    print(f"Optimal schedule: Meet John at {15} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")