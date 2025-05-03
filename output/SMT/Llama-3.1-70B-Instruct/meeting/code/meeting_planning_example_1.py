from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Richmond District
end_time = Int('end_time')  # End time at Financial District
travel_time_richmond_to_financial = 22  # Travel time from Richmond to Financial
travel_time_financial_to_richmond = 21  # Travel time from Financial to Richmond
min_meeting_time = 60  # Minimum meeting time with Betty

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Richmond District is 9:00 AM
    start_time + travel_time_richmond_to_financial >= 17 * 60 + 15,  # Arrive at Financial after 5:15 PM
    end_time >= 17 * 60 + 15,  # Meet Betty after 5:15 PM
    end_time <= 21 * 60 + 45,  # Meet Betty before 9:45 PM
    end_time - (start_time + travel_time_richmond_to_financial) >= min_meeting_time,  # Meet Betty for at least 60 minutes
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
    print(f"Optimal schedule: Meet Betty at {17} hours and {15} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")