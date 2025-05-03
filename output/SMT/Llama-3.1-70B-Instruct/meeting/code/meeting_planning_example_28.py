from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Union Square
end_time = Int('end_time')  # End time at Chinatown
travel_time_union_square_to_chinatown = 7  # Travel time from Union Square to Chinatown
travel_time_chinatown_to_union_square = 7  # Travel time from Chinatown to Union Square
min_meeting_time = 75  # Minimum meeting time with Joshua

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Union Square is 9:00 AM
    start_time + travel_time_union_square_to_chinatown >= 18 * 60,  # Arrive at Chinatown after 6:00 PM
    end_time >= 18 * 60,  # Meet Joshua after 6:00 PM
    end_time <= 21 * 60 + 30,  # Meet Joshua before 9:30 PM
    end_time - (start_time + travel_time_union_square_to_chinatown) >= min_meeting_time,  # Meet Joshua for at least 75 minutes
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
    print(f"Optimal schedule: Meet Joshua at {18} hours and leave at {end_time_value} hours")
else:
    print("No solution found")