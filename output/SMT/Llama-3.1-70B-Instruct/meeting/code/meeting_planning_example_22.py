from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Presidio
end_time = Int('end_time')  # End time at Union Square
travel_time_presidio_to_union_square = 22  # Travel time from Presidio to Union Square
travel_time_union_square_to_presidio = 24  # Travel time from Union Square to Presidio
min_meeting_time = 105  # Minimum meeting time with Andrew

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Presidio is 9:00 AM
    start_time + travel_time_presidio_to_union_square >= 11 * 60 + 15,  # Arrive at Union Square after 11:15 AM
    end_time >= 11 * 60 + 15,  # Meet Andrew after 11:15 AM
    end_time <= 17 * 60 + 15,  # Meet Andrew before 5:15 PM
    end_time - (start_time + travel_time_presidio_to_union_square) >= min_meeting_time,  # Meet Andrew for at least 105 minutes
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
    print(f"Optimal schedule: Meet Andrew at {11} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")