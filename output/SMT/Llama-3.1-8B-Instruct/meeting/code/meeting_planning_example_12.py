from z3 import *

# Define the variables
start_time_barbara = 1800  # 6:00 PM
end_time_barbara = 2130  # 9:30 PM
min_meeting_time = 90  # 1.5 hours
travel_time_north_to_alamo = 16  # 16 minutes
travel_time_alamo_to_north = 15  # 15 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave North Beach to meet Barbara
y = Int('y')  # Time to leave Alamo Square to return to North Beach
z = Int('z')  # Time to meet Barbara

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at North Beach at 9:00 AM
s.add(x + travel_time_north_to_alamo >= start_time_barbara)  # Travel to Alamo Square
s.add(x + travel_time_north_to_alamo + min_meeting_time <= end_time_barbara)  # Meet Barbara for at least 1.5 hours
s.add(z >= start_time_barbara)  # Meet Barbara
s.add(z <= end_time_barbara)  # Meet Barbara
s.add(y >= z)  # Leave Alamo Square after meeting Barbara
s.add(y + travel_time_alamo_to_north <= 24 * 60)  # Return to North Beach by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave North Beach to meet Barbara:", result[x])
print("Time to leave Alamo Square to return to North Beach:", result[y])
print("Time to meet Barbara:", result[z])