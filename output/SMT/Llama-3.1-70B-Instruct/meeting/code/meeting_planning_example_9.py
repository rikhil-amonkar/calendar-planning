from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Union Square
end_time = Int('end_time')  # End time at Nob Hill
travel_time_union_square_to_nob_hill = 9  # Travel time from Union Square to Nob Hill
travel_time_nob_hill_to_union_square = 7  # Travel time from Nob Hill to Union Square
min_meeting_time = 75  # Minimum meeting time with Mary

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Union Square is 9:00 AM
    start_time + travel_time_union_square_to_nob_hill >= 12 * 60,  # Arrive at Nob Hill after 12:00 PM
    end_time >= 12 * 60,  # Meet Mary after 12:00 PM
    end_time <= 16 * 60 + 15,  # Meet Mary before 4:15 PM
    end_time - (start_time + travel_time_union_square_to_nob_hill) >= min_meeting_time,  # Meet Mary for at least 75 minutes
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
    print(f"Optimal schedule: Meet Mary at {12} hours and leave at {end_time_value} hours")
else:
    print("No solution found")