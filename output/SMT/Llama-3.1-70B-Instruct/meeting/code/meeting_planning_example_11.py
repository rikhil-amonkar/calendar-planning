from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Nob Hill
end_time = Int('end_time')  # End time at Sunset District
travel_time_nob_hill_to_sunset = 25  # Travel time from Nob Hill to Sunset
travel_time_sunset_to_nob_hill = 27  # Travel time from Sunset to Nob Hill
min_meeting_time = 75  # Minimum meeting time with Carol

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Nob Hill is 9:00 AM
    start_time + travel_time_nob_hill_to_sunset >= 14 * 60,  # Arrive at Sunset after 2:00 PM
    end_time >= 14 * 60,  # Meet Carol after 2:00 PM
    end_time <= 20 * 60 + 30,  # Meet Carol before 8:30 PM
    end_time - (start_time + travel_time_nob_hill_to_sunset) >= min_meeting_time,  # Meet Carol for at least 75 minutes
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
    print(f"Optimal schedule: Meet Carol at {14} hours and leave at {end_time_value} hours")
else:
    print("No solution found")