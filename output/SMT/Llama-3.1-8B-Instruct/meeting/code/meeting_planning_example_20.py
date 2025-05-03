from z3 import *

# Define the variables
start_time_joseph = 1130  # 11:30 AM
end_time_joseph = 1315  # 1:15 PM
min_meeting_time = 75  # 1.25 hours
travel_time_chinatown_to_nob = 8  # 8 minutes
travel_time_nob_to_chinatown = 6  # 6 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Chinatown to meet Joseph
y = Int('y')  # Time to leave Nob Hill to return to Chinatown
z = Int('z')  # Time to meet Joseph

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Chinatown at 9:00 AM
s.add(x + travel_time_chinatown_to_nob >= start_time_joseph)  # Travel to Nob Hill
s.add(x + travel_time_chinatown_to_nob + min_meeting_time <= end_time_joseph)  # Meet Joseph for at least 1.25 hours
s.add(z >= start_time_joseph)  # Meet Joseph
s.add(z <= end_time_joseph)  # Meet Joseph
s.add(y >= z)  # Leave Nob Hill after meeting Joseph
s.add(y + travel_time_nob_to_chinatown <= 15 * 60)  # Return to Chinatown by 3:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Chinatown to meet Joseph:", result[x])
print("Time to leave Nob Hill to return to Chinatown:", result[y])
print("Time to meet Joseph:", result[z])