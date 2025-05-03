from z3 import *

# Define the variables
start_time_william = 1315  # 1:15 PM
end_time_william = 2130  # 9:30 PM
min_meeting_time = 15  # 15 minutes
travel_time_north_to_russian = 4  # 4 minutes
travel_time_russian_to_north = 5  # 5 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave North Beach to meet William
y = Int('y')  # Time to leave Russian Hill to return to North Beach
z = Int('z')  # Time to meet William

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at North Beach at 9:00 AM
s.add(x + travel_time_north_to_russian >= start_time_william)  # Travel to Russian Hill
s.add(x + travel_time_north_to_russian + min_meeting_time <= end_time_william)  # Meet William for at least 15 minutes
s.add(z >= start_time_william)  # Meet William
s.add(z <= end_time_william)  # Meet William
s.add(y >= z)  # Leave Russian Hill after meeting William
s.add(y + travel_time_russian_to_north <= 24 * 60)  # Return to North Beach by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave North Beach to meet William:", result[x])
print("Time to leave Russian Hill to return to North Beach:", result[y])
print("Time to meet William:", result[z])