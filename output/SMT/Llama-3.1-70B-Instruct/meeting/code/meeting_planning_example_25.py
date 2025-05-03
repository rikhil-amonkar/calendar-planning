from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Golden Gate Park
end_time = Int('end_time')  # End time at Chinatown
travel_time_golden_gate_park_to_chinatown = 23  # Travel time from Golden Gate Park to Chinatown
travel_time_chinatown_to_golden_gate_park = 23  # Travel time from Chinatown to Golden Gate Park
min_meeting_time = 105  # Minimum meeting time with David

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Golden Gate Park is 9:00 AM
    start_time + travel_time_golden_gate_park_to_chinatown >= 16 * 60,  # Arrive at Chinatown after 4:00 PM
    end_time >= 16 * 60,  # Meet David after 4:00 PM
    end_time <= 21 * 60 + 45,  # Meet David before 9:45 PM
    end_time - (start_time + travel_time_golden_gate_park_to_chinatown) >= min_meeting_time,  # Meet David for at least 105 minutes
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
    print(f"Optimal schedule: Meet David at {16} hours and leave at {end_time_value} hours")
else:
    print("No solution found")