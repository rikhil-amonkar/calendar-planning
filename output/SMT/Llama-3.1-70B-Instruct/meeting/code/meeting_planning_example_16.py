from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Chinatown
end_time = Int('end_time')  # End time at Russian Hill
travel_time_chinatown_to_russian_hill = 7  # Travel time from Chinatown to Russian Hill
travel_time_russian_hill_to_chinatown = 9  # Travel time from Russian Hill to Chinatown
min_meeting_time = 105  # Minimum meeting time with Ronald

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Chinatown is 9:00 AM
    start_time + travel_time_chinatown_to_russian_hill >= 15 * 60 + 15,  # Arrive at Russian Hill after 3:15 PM
    end_time >= 15 * 60 + 15,  # Meet Ronald after 3:15 PM
    end_time <= 21 * 60 + 30,  # Meet Ronald before 9:30 PM
    end_time - (start_time + travel_time_chinatown_to_russian_hill) >= min_meeting_time,  # Meet Ronald for at least 105 minutes
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
    print(f"Optimal schedule: Meet Ronald at {15} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")