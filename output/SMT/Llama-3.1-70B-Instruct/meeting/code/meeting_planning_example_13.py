from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Presidio
end_time = Int('end_time')  # End time at North Beach
travel_time_presidio_to_north_beach = 18  # Travel time from Presidio to North Beach
travel_time_north_beach_to_presidio = 17  # Travel time from North Beach to Presidio
min_meeting_time = 75  # Minimum meeting time with Betty

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Presidio is 9:00 AM
    start_time + travel_time_presidio_to_north_beach >= 18 * 60 + 45,  # Arrive at North Beach after 6:45 PM
    end_time >= 18 * 60 + 45,  # Meet Betty after 6:45 PM
    end_time <= 22 * 60,  # Meet Betty before 10:00 PM
    end_time - (start_time + travel_time_presidio_to_north_beach) >= min_meeting_time,  # Meet Betty for at least 75 minutes
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
    print(f"Optimal schedule: Meet Betty at {18} hours and {45} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")