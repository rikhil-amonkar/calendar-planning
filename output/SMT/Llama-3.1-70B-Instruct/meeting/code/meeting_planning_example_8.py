from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Chinatown
end_time = Int('end_time')  # End time at Marina District
travel_time_chinatown_to_marina = 12  # Travel time from Chinatown to Marina
travel_time_marina_to_chinatown = 16  # Travel time from Marina to Chinatown
min_meeting_time = 105  # Minimum meeting time with Stephanie

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Chinatown is 9:00 AM
    start_time + travel_time_chinatown_to_marina >= 8 * 60,  # Arrive at Marina after 8:00 AM
    end_time >= 8 * 60,  # Meet Stephanie after 8:00 AM
    end_time <= 15 * 60,  # Meet Stephanie before 3:00 PM
    end_time - (start_time + travel_time_chinatown_to_marina) >= min_meeting_time,  # Meet Stephanie for at least 105 minutes
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
    print(f"Optimal schedule: Meet Stephanie at {start_time_value} hours and leave at {end_time_value} hours")
else:
    print("No solution found")