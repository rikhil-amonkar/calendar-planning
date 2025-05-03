from z3 import *

# Define the variables
start_time_ronald = 1315  # 3:15 PM
end_time_ronald = 2130  # 9:30 PM
min_meeting_time = 105  # 1.75 hours
travel_time_chinatown_to_russian = 7  # 7 minutes
travel_time_russian_to_chinatown = 9  # 9 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Chinatown to meet Ronald
y = Int('y')  # Time to leave Russian Hill to return to Chinatown
z = Int('z')  # Time to meet Ronald

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Chinatown at 9:00 AM
s.add(x + travel_time_chinatown_to_russian >= start_time_ronald)  # Travel to Russian Hill
s.add(x + travel_time_chinatown_to_russian + min_meeting_time <= end_time_ronald)  # Meet Ronald for at least 1.75 hours
s.add(z >= start_time_ronald)  # Meet Ronald
s.add(z <= end_time_ronald)  # Meet Ronald
s.add(y >= z)  # Leave Russian Hill after meeting Ronald
s.add(y + travel_time_russian_to_chinatown <= 23 * 60)  # Return to Chinatown by 11:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Chinatown to meet Ronald:", result[x])
print("Time to leave Russian Hill to return to Chinatown:", result[y])
print("Time to meet Ronald:", result[z])