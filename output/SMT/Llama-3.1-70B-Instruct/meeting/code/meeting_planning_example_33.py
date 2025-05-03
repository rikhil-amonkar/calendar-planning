from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Sunset District
end_time = Int('end_time')  # End time at Union Square
travel_time_sunset_to_union_square = 30  # Travel time from Sunset to Union Square
travel_time_union_square_to_sunset = 26  # Travel time from Union Square to Sunset
min_meeting_time = 15  # Minimum meeting time with Sarah

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Sunset District is 9:00 AM
    start_time + travel_time_sunset_to_union_square >= 12 * 60 + 30,  # Arrive at Union Square after 12:30 PM
    end_time >= 12 * 60 + 30,  # Meet Sarah after 12:30 PM
    end_time <= 21 * 60 + 30,  # Meet Sarah before 9:30 PM
    end_time - (start_time + travel_time_sunset_to_union_square) >= min_meeting_time,  # Meet Sarah for at least 15 minutes
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
    print(f"Optimal schedule: Meet Sarah at {12} hours and {30} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")