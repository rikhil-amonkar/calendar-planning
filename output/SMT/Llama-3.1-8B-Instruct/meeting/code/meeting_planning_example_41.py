from z3 import *

# Define the variables
start_time_george = 0  # 7:30 AM
end_time_george = 0915  # 1:15 PM
min_meeting_time = 45  # 45 minutes
travel_time_north_to_haight = 18  # 18 minutes
travel_time_haight_to_north = 19  # 19 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave North Beach to meet George
y = Int('y')  # Time to leave Haight-Ashbury to return to North Beach
z = Int('z')  # Time to meet George

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at North Beach at 9:00 AM
s.add(x + travel_time_north_to_haight >= start_time_george)  # Travel to Haight-Ashbury
s.add(x + travel_time_north_to_haight + min_meeting_time <= end_time_george)  # Meet George for at least 45 minutes
s.add(z >= start_time_george)  # Meet George
s.add(z <= end_time_george)  # Meet George
s.add(y >= z)  # Leave Haight-Ashbury after meeting George
s.add(y + travel_time_haight_to_north <= 11 * 60)  # Return to North Beach by 11:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave North Beach to meet George:", result[x])
print("Time to leave Haight-Ashbury to return to North Beach:", result[y])
print("Time to meet George:", result[z])