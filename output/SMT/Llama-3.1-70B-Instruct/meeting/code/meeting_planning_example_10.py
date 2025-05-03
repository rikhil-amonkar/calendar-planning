from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Golden Gate Park
end_time = Int('end_time')  # End time at Marina District
travel_time_golden_gate_park_to_marina = 16  # Travel time from Golden Gate Park to Marina
travel_time_marina_to_golden_gate_park = 18  # Travel time from Marina to Golden Gate Park
min_meeting_time = 15  # Minimum meeting time with James

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Golden Gate Park is 9:00 AM
    start_time + travel_time_golden_gate_park_to_marina >= 10 * 60 + 15,  # Arrive at Marina after 10:15 AM
    end_time >= 10 * 60 + 15,  # Meet James after 10:15 AM
    end_time <= 13 * 60 + 30,  # Meet James before 1:30 PM
    end_time - (start_time + travel_time_golden_gate_park_to_marina) >= min_meeting_time,  # Meet James for at least 15 minutes
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
    print(f"Optimal schedule: Meet James at {10} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")