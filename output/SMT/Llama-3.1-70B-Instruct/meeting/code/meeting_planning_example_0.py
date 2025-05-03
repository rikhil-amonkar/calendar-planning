from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Marina District
end_time = Int('end_time')  # End time at Mission District
travel_time_marina_to_mission = 20  # Travel time from Marina to Mission
travel_time_mission_to_marina = 19  # Travel time from Mission to Marina
min_meeting_time = 120  # Minimum meeting time with Stephanie

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Marina District is 9:00 AM
    start_time + travel_time_marina_to_mission <= 10 * 60 + 30,  # Arrive at Mission before 10:30 AM
    end_time >= 10 * 60 + 30,  # Meet Stephanie after 10:30 AM
    end_time <= 13 * 60 + 30,  # Meet Stephanie before 1:30 PM
    end_time - (start_time + travel_time_marina_to_mission) >= min_meeting_time,  # Meet Stephanie for at least 120 minutes
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
    print(f"Optimal schedule: Meet Stephanie at {start_time_value} and leave at {end_time_value}")
else:
    print("No solution found")