from z3 import *

# Define the variables
start_time_joshua = 615  # 10:15 AM
end_time_joshua = 1200  # 1:00 PM
min_meeting_time = 45  # 45 minutes
travel_time_chinatown_to_nob = 8  # 8 minutes
travel_time_nob_to_chinatown = 6  # 6 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Chinatown to meet Joshua
y = Int('y')  # Time to leave Nob Hill to return to Chinatown
z = Int('z')  # Time to meet Joshua

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Chinatown at 9:00 AM
s.add(x + travel_time_chinatown_to_nob >= start_time_joshua)  # Travel to Nob Hill
s.add(x + travel_time_chinatown_to_nob + min_meeting_time <= end_time_joshua)  # Meet Joshua for at least 45 minutes
s.add(z >= start_time_joshua)  # Meet Joshua
s.add(z <= end_time_joshua)  # Meet Joshua
s.add(y >= z)  # Leave Nob Hill after meeting Joshua
s.add(y + travel_time_nob_to_chinatown <= 11 * 60)  # Return to Chinatown by 11:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Chinatown to meet Joshua:", result[x])
print("Time to leave Nob Hill to return to Chinatown:", result[y])
print("Time to meet Joshua:", result[z])