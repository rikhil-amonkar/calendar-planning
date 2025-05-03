from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Sunset District
end_time = Int('end_time')  # End time at Haight-Ashbury
travel_time_sunset_to_haight = 15  # Travel time from Sunset to Haight-Ashbury
travel_time_haight_to_sunset = 15  # Travel time from Haight-Ashbury to Sunset
min_meeting_time = 75  # Minimum meeting time with Nancy

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Sunset District is 9:00 AM
    start_time + travel_time_sunset_to_haight >= 19 * 60 + 30,  # Arrive at Haight-Ashbury after 7:30 PM
    end_time >= 19 * 60 + 30,  # Meet Nancy after 7:30 PM
    end_time <= 21 * 60 + 45,  # Meet Nancy before 9:45 PM
    end_time - (start_time + travel_time_sunset_to_haight) >= min_meeting_time,  # Meet Nancy for at least 75 minutes
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
    print(f"Optimal schedule: Meet Nancy at {19} hours and {30} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")