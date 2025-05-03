from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Bayview
end_time = Int('end_time')  # End time at Golden Gate Park
travel_time_bayview_to_golden_gate = 22  # Travel time from Bayview to Golden Gate Park
travel_time_golden_gate_to_bayview = 23  # Travel time from Golden Gate Park to Bayview
min_meeting_time = 90  # Minimum meeting time with Barbara

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Bayview is 9:00 AM
    start_time + travel_time_bayview_to_golden_gate <= 11 * 60 + 30,  # Arrive at Golden Gate Park before 11:30 AM
    end_time >= 8 * 60,  # Meet Barbara after 8:00 AM
    end_time <= 11 * 60 + 30,  # Meet Barbara before 11:30 AM
    end_time - (start_time + travel_time_bayview_to_golden_gate) >= min_meeting_time,  # Meet Barbara for at least 90 minutes
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
    print(f"Optimal schedule: Meet Barbara at {start_time_value} hours and leave at {end_time_value} hours")
else:
    print("No solution found")