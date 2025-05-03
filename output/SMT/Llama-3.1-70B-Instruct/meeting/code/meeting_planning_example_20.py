from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Chinatown
end_time = Int('end_time')  # End time at Nob Hill
travel_time_chinatown_to_nob_hill = 8  # Travel time from Chinatown to Nob Hill
travel_time_nob_hill_to_chinatown = 6  # Travel time from Nob Hill to Chinatown
min_meeting_time = 75  # Minimum meeting time with Joseph

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Chinatown is 9:00 AM
    start_time + travel_time_chinatown_to_nob_hill >= 11 * 60 + 30,  # Arrive at Nob Hill after 11:30 AM
    end_time >= 11 * 60 + 30,  # Meet Joseph after 11:30 AM
    end_time <= 15 * 60 + 15,  # Meet Joseph before 3:15 PM
    end_time - (start_time + travel_time_chinatown_to_nob_hill) >= min_meeting_time,  # Meet Joseph for at least 75 minutes
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
    print(f"Optimal schedule: Meet Joseph at {11} hours and {30} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")