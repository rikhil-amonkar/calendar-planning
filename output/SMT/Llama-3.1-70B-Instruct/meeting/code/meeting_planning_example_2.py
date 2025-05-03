from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Haight-Ashbury
end_time = Int('end_time')  # End time at Sunset District
travel_time_haight_to_sunset = 15  # Travel time from Haight-Ashbury to Sunset
travel_time_sunset_to_haight = 15  # Travel time from Sunset to Haight-Ashbury
min_meeting_time = 90  # Minimum meeting time with Jessica

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Haight-Ashbury is 9:00 AM
    start_time + travel_time_haight_to_sunset >= 15 * 60 + 15,  # Arrive at Sunset after 3:15 PM
    end_time >= 15 * 60 + 15,  # Meet Jessica after 3:15 PM
    end_time <= 20 * 60 + 15,  # Meet Jessica before 8:15 PM
    end_time - (start_time + travel_time_haight_to_sunset) >= min_meeting_time,  # Meet Jessica for at least 90 minutes
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
    print(f"Optimal schedule: Meet Jessica at {15} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")