from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Bayview
end_time = Int('end_time')  # End time at Russian Hill
travel_time_bayview_to_russian_hill = 23  # Travel time from Bayview to Russian Hill
travel_time_russian_hill_to_bayview = 23  # Travel time from Russian Hill to Bayview
min_meeting_time = 75  # Minimum meeting time with John

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Bayview is 9:00 AM
    start_time + travel_time_bayview_to_russian_hill >= 17 * 60 + 30,  # Arrive at Russian Hill after 5:30 PM
    end_time >= 17 * 60 + 30,  # Meet John after 5:30 PM
    end_time <= 21 * 60,  # Meet John before 9:00 PM
    end_time - (start_time + travel_time_bayview_to_russian_hill) >= min_meeting_time,  # Meet John for at least 75 minutes
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
    print(f"Optimal schedule: Meet John at {17} hours and {30} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")