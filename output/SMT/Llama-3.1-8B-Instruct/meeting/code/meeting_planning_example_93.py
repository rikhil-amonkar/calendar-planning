from z3 import *

# Define the variables
start_time_emily = 1900  # 7:00 PM
end_time_emily = 2100  # 9:00 PM
min_meeting_time = 75  # 1.25 hours
travel_time_north_to_chinatown = 6  # 6 minutes
travel_time_chinatown_to_north = 3  # 3 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave North Beach to meet Emily
y = Int('y')  # Time to leave Chinatown to return to North Beach
z = Int('z')  # Time to meet Emily

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at North Beach at 9:00 AM
s.add(x + travel_time_north_to_chinatown >= start_time_emily)  # Travel to Chinatown
s.add(x + travel_time_north_to_chinatown + min_meeting_time <= end_time_emily)  # Meet Emily for at least 1.25 hours
s.add(z >= start_time_emily)  # Meet Emily
s.add(z <= end_time_emily)  # Meet Emily
s.add(y >= z)  # Leave Chinatown after meeting Emily
s.add(y + travel_time_chinatown_to_north <= 24 * 60)  # Return to North Beach by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave North Beach to meet Emily:", result[x])
print("Time to leave Chinatown to return to North Beach:", result[y])
print("Time to meet Emily:", result[z])