from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Golden Gate Park
end_time = Int('end_time')  # End time at Pacific Heights
travel_time_golden_gate_park_to_pacific_heights = 16  # Travel time from Golden Gate Park to Pacific Heights
travel_time_pacific_heights_to_golden_gate_park = 15  # Travel time from Pacific Heights to Golden Gate Park
min_meeting_time = 45  # Minimum meeting time with John

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Golden Gate Park is 9:00 AM
    start_time + travel_time_golden_gate_park_to_pacific_heights >= 19 * 60 + 45,  # Arrive at Pacific Heights after 7:45 PM
    end_time >= 19 * 60 + 45,  # Meet John after 7:45 PM
    end_time <= 20 * 60 + 45,  # Meet John before 8:45 PM
    end_time - (start_time + travel_time_golden_gate_park_to_pacific_heights) >= min_meeting_time,  # Meet John for at least 45 minutes
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
    print(f"Optimal schedule: Meet John at {19} hours and {45} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")