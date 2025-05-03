from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at Alamo Square
end_time = Int('end_time')  # End time at Sunset District
travel_time_alamo_square_to_sunset = 16  # Travel time from Alamo Square to Sunset
travel_time_sunset_to_alamo_square = 17  # Travel time from Sunset to Alamo Square
min_meeting_time = 15  # Minimum meeting time with Matthew

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at Alamo Square is 9:00 AM
    start_time + travel_time_alamo_square_to_sunset >= 13 * 60 + 30,  # Arrive at Sunset after 1:30 PM
    end_time >= 13 * 60 + 30,  # Meet Matthew after 1:30 PM
    end_time <= 14 * 60 + 30,  # Meet Matthew before 2:30 PM
    end_time - (start_time + travel_time_alamo_square_to_sunset) >= min_meeting_time,  # Meet Matthew for at least 15 minutes
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
    print(f"Optimal schedule: Meet Matthew at {13} hours and {30} minutes and leave at {end_time_value} hours")
else:
    print("No solution found")