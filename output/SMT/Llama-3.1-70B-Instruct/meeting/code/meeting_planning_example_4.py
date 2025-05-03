from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Presidio
end_time = Int('end_time')  # End time at Marina District
travel_time_presidio_to_marina = 10  # Travel time from Presidio to Marina
travel_time_marina_to_presidio = 10  # Travel time from Marina to Presidio
min_meeting_time = 60  # Minimum meeting time with Jessica

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Presidio is 9:00 AM
    start_time + travel_time_presidio_to_marina >= 9 * 60 + 15,  # Arrive at Marina after 9:15 AM
    end_time >= 9 * 60 + 15,  # Meet Jessica after 9:15 AM
    end_time <= 17 * 60 + 45,  # Meet Jessica before 5:45 PM
    end_time - (start_time + travel_time_presidio_to_marina) >= min_meeting_time,  # Meet Jessica for at least 60 minutes
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
    print(f"Optimal schedule: Meet Jessica at {9} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")