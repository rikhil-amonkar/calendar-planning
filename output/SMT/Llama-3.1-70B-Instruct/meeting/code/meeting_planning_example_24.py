from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Nob Hill
end_time = Int('end_time')  # End time at Presidio
travel_time_nob_hill_to_presidio = 17  # Travel time from Nob Hill to Presidio
travel_time_presidio_to_nob_hill = 18  # Travel time from Presidio to Nob Hill
min_meeting_time = 30  # Minimum meeting time with Matthew

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Nob Hill is 9:00 AM
    start_time + travel_time_nob_hill_to_presidio >= 11 * 60,  # Arrive at Presidio after 11:00 AM
    end_time >= 11 * 60,  # Meet Matthew after 11:00 AM
    end_time <= 15 * 60 + 15,  # Meet Matthew before 3:15 PM
    end_time - (start_time + travel_time_nob_hill_to_presidio) >= min_meeting_time,  # Meet Matthew for at least 30 minutes
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
    print(f"Optimal schedule: Meet Matthew at {11} hours and leave at {end_time_value} hours")
else:
    print("No solution found")