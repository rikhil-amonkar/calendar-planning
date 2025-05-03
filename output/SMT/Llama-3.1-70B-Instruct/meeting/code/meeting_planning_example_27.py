from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Marina District
end_time = Int('end_time')  # End time at Pacific Heights
travel_time_marina_to_pacific_heights = 7  # Travel time from Marina to Pacific Heights
travel_time_pacific_heights_to_marina = 6  # Travel time from Pacific Heights to Marina
min_meeting_time = 15  # Minimum meeting time with Margaret

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Marina District is 9:00 AM
    start_time + travel_time_marina_to_pacific_heights >= 19 * 60,  # Arrive at Pacific Heights after 7:00 PM
    end_time >= 19 * 60,  # Meet Margaret after 7:00 PM
    end_time <= 19 * 60 + 45,  # Meet Margaret before 7:45 PM
    end_time - (start_time + travel_time_marina_to_pacific_heights) >= min_meeting_time,  # Meet Margaret for at least 15 minutes
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
    print(f"Optimal schedule: Meet Margaret at {19} hours and leave at {end_time_value} hours")
else:
    print("No solution found")