from z3 import *

# Define the variables
start_time_mark = 0  # 8:00 AM
end_time_mark = 1145  # 12:45 PM
min_meeting_time = 90  # 1.5 hours
travel_time_chinatown_to_union = 7  # 7 minutes
travel_time_union_to_chinatown = 7  # 7 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Chinatown to meet Mark
y = Int('y')  # Time to leave Union Square to return to Chinatown
z = Int('z')  # Time to meet Mark

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Chinatown at 9:00 AM
s.add(x + travel_time_chinatown_to_union >= start_time_mark)  # Travel to Union Square
s.add(x + travel_time_chinatown_to_union + min_meeting_time <= end_time_mark)  # Meet Mark for at least 1.5 hours
s.add(z >= start_time_mark)  # Meet Mark
s.add(z <= end_time_mark)  # Meet Mark
s.add(y >= z)  # Leave Union Square after meeting Mark
s.add(y + travel_time_union_to_chinatown <= 12 * 60)  # Return to Chinatown by 12:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Chinatown to meet Mark:", result[x])
print("Time to leave Union Square to return to Chinatown:", result[y])
print("Time to meet Mark:", result[z])