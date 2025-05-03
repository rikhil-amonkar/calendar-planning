from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time at North Beach
end_time = Int('end_time')  # End time at Alamo Square
travel_time_north_beach_to_alamo_square = 16  # Travel time from North Beach to Alamo Square
travel_time_alamo_square_to_north_beach = 15  # Travel time from Alamo Square to North Beach
min_meeting_time = 90  # Minimum meeting time with Barbara

# Define the constraints
constraints = [
    start_time >= 9 * 60,  # Start time at North Beach is 9:00 AM
    start_time + travel_time_north_beach_to_alamo_square >= 18 * 60,  # Arrive at Alamo Square after 6:00 PM
    end_time >= 18 * 60,  # Meet Barbara after 6:00 PM
    end_time <= 21 * 60 + 30,  # Meet Barbara before 9:30 PM
    end_time - (start_time + travel_time_north_beach_to_alamo_square) >= min_meeting_time,  # Meet Barbara for at least 90 minutes
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
    print(f"Optimal schedule: Meet Barbara at {18} hours and leave at {end_time_value} hours")
else:
    print("No solution found")