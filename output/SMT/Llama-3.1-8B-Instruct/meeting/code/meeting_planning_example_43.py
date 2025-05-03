from z3 import *

# Define the variables
start_time_sandra = 0  # 9:00 AM
end_time_sandra = 1145  # 11:45 AM
min_meeting_time = 15  # 15 minutes
travel_time_marina_to_chinatown = 16  # 16 minutes
travel_time_chinatown_to_marina = 12  # 12 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Marina District to meet Sandra
y = Int('y')  # Time to leave Chinatown to return to Marina District
z = Int('z')  # Time to meet Sandra

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Marina District at 9:00 AM
s.add(x + travel_time_marina_to_chinatown >= start_time_sandra)  # Travel to Chinatown
s.add(x + travel_time_marina_to_chinatown + min_meeting_time <= end_time_sandra)  # Meet Sandra for at least 15 minutes
s.add(z >= start_time_sandra)  # Meet Sandra
s.add(z <= end_time_sandra)  # Meet Sandra
s.add(y >= z)  # Leave Chinatown after meeting Sandra
s.add(y + travel_time_chinatown_to_marina <= 11 * 60)  # Return to Marina District by 11:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Marina District to meet Sandra:", result[x])
print("Time to leave Chinatown to return to Marina District:", result[y])
print("Time to meet Sandra:", result[z])