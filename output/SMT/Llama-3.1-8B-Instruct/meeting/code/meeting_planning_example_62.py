from z3 import *

# Define the variables
start_time_amanda = 1230  # 11:30 AM
end_time_amanda = 2155  # 9:15 PM
min_meeting_time = 15  # 15 minutes
travel_time_presidio_to_russian = 14  # 14 minutes
travel_time_russian_to_presidio = 14  # 14 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Presidio to meet Amanda
y = Int('y')  # Time to leave Russian Hill to return to Presidio
z = Int('z')  # Time to meet Amanda

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Presidio at 9:00 AM
s.add(x + travel_time_presidio_to_russian >= start_time_amanda)  # Travel to Russian Hill
s.add(x + travel_time_presidio_to_russian + min_meeting_time <= end_time_amanda)  # Meet Amanda for at least 15 minutes
s.add(z >= start_time_amanda)  # Meet Amanda
s.add(z <= end_time_amanda)  # Meet Amanda
s.add(y >= z)  # Leave Russian Hill after meeting Amanda
s.add(y + travel_time_russian_to_presidio <= 24 * 60)  # Return to Presidio by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Presidio to meet Amanda:", result[x])
print("Time to leave Russian Hill to return to Presidio:", result[y])
print("Time to meet Amanda:", result[z])