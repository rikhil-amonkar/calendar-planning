from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Fisherman's Wharf
end_time = Int('end_time')  # End time at Nob Hill
travel_time_fishermans_wharf_to_nob_hill = 11  # Travel time from Fisherman's Wharf to Nob Hill
travel_time_nob_hill_to_fishermans_wharf = 11  # Travel time from Nob Hill to Fisherman's Wharf
min_meeting_time = 90  # Minimum meeting time with Kenneth

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Fisherman's Wharf is 9:00 AM
    start_time + travel_time_fishermans_wharf_to_nob_hill >= 14 * 60 + 15,  # Arrive at Nob Hill after 2:15 PM
    end_time >= 14 * 60 + 15,  # Meet Kenneth after 2:15 PM
    end_time <= 19 * 60 + 45,  # Meet Kenneth before 7:45 PM
    end_time - (start_time + travel_time_fishermans_wharf_to_nob_hill) >= min_meeting_time,  # Meet Kenneth for at least 90 minutes
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
    print(f"Optimal schedule: Meet Kenneth at {14} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")