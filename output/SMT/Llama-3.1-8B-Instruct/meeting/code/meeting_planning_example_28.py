from z3 import *

# Define the variables
start_time_joshua = 1800  # 6:00 PM
end_time_joshua = 2130  # 9:30 PM
min_meeting_time = 75  # 1.25 hours
travel_time_union_to_chinatown = 7  # 7 minutes
travel_time_chinatown_to_union = 7  # 7 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Union Square to meet Joshua
y = Int('y')  # Time to leave Chinatown to return to Union Square
z = Int('z')  # Time to meet Joshua

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Union Square at 9:00 AM
s.add(x + travel_time_union_to_chinatown >= start_time_joshua)  # Travel to Chinatown
s.add(x + travel_time_union_to_chinatown + min_meeting_time <= end_time_joshua)  # Meet Joshua for at least 1.25 hours
s.add(z >= start_time_joshua)  # Meet Joshua
s.add(z <= end_time_joshua)  # Meet Joshua
s.add(y >= z)  # Leave Chinatown after meeting Joshua
s.add(y + travel_time_chinatown_to_union <= 24 * 60)  # Return to Union Square by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Union Square to meet Joshua:", result[x])
print("Time to leave Chinatown to return to Union Square:", result[y])
print("Time to meet Joshua:", result[z])