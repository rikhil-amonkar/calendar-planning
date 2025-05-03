from z3 import *

# Define the variables
start_time_sarah = 1230  # 12:30 PM
end_time_sarah = 2130  # 9:30 PM
min_meeting_time = 15  # 15 minutes
travel_time_sunset_to_union = 30  # 30 minutes
travel_time_union_to_sunset = 26  # 26 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Sunset District to meet Sarah
y = Int('y')  # Time to leave Union Square to return to Sunset District
z = Int('z')  # Time to meet Sarah

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Sunset District at 9:00 AM
s.add(x + travel_time_sunset_to_union >= start_time_sarah)  # Travel to Union Square
s.add(x + travel_time_sunset_to_union + min_meeting_time <= end_time_sarah)  # Meet Sarah for at least 15 minutes
s.add(z >= start_time_sarah)  # Meet Sarah
s.add(z <= end_time_sarah)  # Meet Sarah
s.add(y >= z)  # Leave Union Square after meeting Sarah
s.add(y + travel_time_union_to_sunset <= 23 * 60)  # Return to Sunset District by 11:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Sunset District to meet Sarah:", result[x])
print("Time to leave Union Square to return to Sunset District:", result[y])
print("Time to meet Sarah:", result[z])