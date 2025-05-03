from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Russian Hill
end_time = Int('end_time')  # End time at Golden Gate Park
travel_time_russian_hill_to_golden_gate = 21  # Travel time from Russian Hill to Golden Gate Park
travel_time_golden_gate_to_russian_hill = 19  # Travel time from Golden Gate Park to Russian Hill
min_meeting_time = 90  # Minimum meeting time with John

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Russian Hill is 9:00 AM
    start_time + travel_time_russian_hill_to_golden_gate >= 13 * 60,  # Arrive at Golden Gate Park after 1:00 PM
    end_time >= 13 * 60,  # Meet John after 1:00 PM
    end_time <= 18 * 60 + 15,  # Meet John before 6:15 PM
    end_time - (start_time + travel_time_russian_hill_to_golden_gate) >= min_meeting_time,  # Meet John for at least 90 minutes
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
    print(f"Optimal schedule: Meet John at {13} hours and leave at {end_time_value} hours")
else:
    print("No solution found")