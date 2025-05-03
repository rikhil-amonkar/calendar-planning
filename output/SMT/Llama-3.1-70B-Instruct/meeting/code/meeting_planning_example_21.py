from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Mission District
end_time = Int('end_time')  # End time at Haight-Ashbury
travel_time_mission_to_haight = 12  # Travel time from Mission to Haight-Ashbury
travel_time_haight_to_mission = 11  # Travel time from Haight-Ashbury to Mission
min_meeting_time = 30  # Minimum meeting time with Margaret

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Mission District is 9:00 AM
    start_time + travel_time_mission_to_haight >= 8 * 60,  # Arrive at Haight-Ashbury after 8:00 AM
    end_time >= 8 * 60,  # Meet Margaret after 8:00 AM
    end_time <= 15 * 60 + 45,  # Meet Margaret before 3:45 PM
    end_time - (start_time + travel_time_mission_to_haight) >= min_meeting_time,  # Meet Margaret for at least 30 minutes
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
    print(f"Optimal schedule: Meet Margaret at {9} hours and leave at {end_time_value} hours")
else:
    print("No solution found")