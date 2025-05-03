from z3 import *

# Define the variables
start_time_sarah = 1115  # 1:15 PM
end_time_sarah = 1315  # 1:15 PM
min_meeting_time = 105  # 1.75 hours
travel_time_richmond_to_presidio = 7  # 7 minutes
travel_time_presidio_to_richmond = 7  # 7 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Richmond District to meet Sarah
y = Int('y')  # Time to leave Presidio to return to Richmond District
z = Int('z')  # Time to meet Sarah

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Richmond District at 9:00 AM
s.add(x + travel_time_richmond_to_presidio >= start_time_sarah)  # Travel to Presidio
s.add(x + travel_time_richmond_to_presidio + min_meeting_time <= end_time_sarah)  # Meet Sarah for at least 1.75 hours
s.add(z >= start_time_sarah)  # Meet Sarah
s.add(z <= end_time_sarah)  # Meet Sarah
s.add(y >= z)  # Leave Presidio after meeting Sarah
s.add(y + travel_time_presidio_to_richmond <= 13 * 60)  # Return to Richmond District by 1:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Richmond District to meet Sarah:", result[x])
print("Time to leave Presidio to return to Richmond District:", result[y])
print("Time to meet Sarah:", result[z])