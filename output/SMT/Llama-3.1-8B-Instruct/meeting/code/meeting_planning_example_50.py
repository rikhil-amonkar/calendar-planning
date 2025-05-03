from z3 import *

# Define the variables
start_time_melissa = 0  # 9:30 AM
end_time_melissa = 2130  # 8:30 PM
min_meeting_time = 75  # 1.25 hours
travel_time_north_to_nob = 7  # 7 minutes
travel_time_nob_to_north = 8  # 8 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave North Beach to meet Melissa
y = Int('y')  # Time to leave Nob Hill to return to North Beach
z = Int('z')  # Time to meet Melissa

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at North Beach at 9:00 AM
s.add(x + travel_time_north_to_nob >= start_time_melissa)  # Travel to Nob Hill
s.add(x + travel_time_north_to_nob + min_meeting_time <= end_time_melissa)  # Meet Melissa for at least 1.25 hours
s.add(z >= start_time_melissa)  # Meet Melissa
s.add(z <= end_time_melissa)  # Meet Melissa
s.add(y >= z)  # Leave Nob Hill after meeting Melissa
s.add(y + travel_time_nob_to_north <= 23 * 60)  # Return to North Beach by 11:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave North Beach to meet Melissa:", result[x])
print("Time to leave Nob Hill to return to North Beach:", result[y])
print("Time to meet Melissa:", result[z])