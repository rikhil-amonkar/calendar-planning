from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Richmond District
end_time = Int('end_time')  # End time at North Beach
travel_time_richmond_to_north_beach = 17  # Travel time from Richmond to North Beach
travel_time_north_beach_to_richmond = 18  # Travel time from North Beach to Richmond
min_meeting_time = 120  # Minimum meeting time with Stephanie

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Richmond District is 9:00 AM
    start_time + travel_time_richmond_to_north_beach >= 9 * 60 + 30,  # Arrive at North Beach after 9:30 AM
    end_time >= 9 * 60 + 30,  # Meet Stephanie after 9:30 AM
    end_time <= 16 * 60 + 15,  # Meet Stephanie before 4:15 PM
    end_time - (start_time + travel_time_richmond_to_north_beach) >= min_meeting_time,  # Meet Stephanie for at least 120 minutes
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
    print(f"Optimal schedule: Meet Stephanie at {9} hours and {30} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")