from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at The Castro
end_time = Int('end_time')  # End time at Golden Gate Park
travel_time_castro_to_golden_gate = 11  # Travel time from The Castro to Golden Gate Park
travel_time_golden_gate_to_castro = 13  # Travel time from Golden Gate Park to The Castro
min_meeting_time = 105  # Minimum meeting time with Jeffrey

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at The Castro is 9:00 AM
    start_time + travel_time_castro_to_golden_gate >= 7 * 60,  # Arrive at Golden Gate Park after 7:00 AM
    end_time >= 7 * 60,  # Meet Jeffrey after 7:00 AM
    end_time <= 17 * 60 + 30,  # Meet Jeffrey before 5:30 PM
    end_time - (start_time + travel_time_castro_to_golden_gate) >= min_meeting_time,  # Meet Jeffrey for at least 105 minutes
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
    print(f"Optimal schedule: Meet Jeffrey at {7} hours and leave at {end_time_value} hours")
else:
    print("No solution found")