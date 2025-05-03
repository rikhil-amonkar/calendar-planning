from z3 import *

# Define the variables
start_time_andrew = 1115  # 11:15 AM
end_time_andrew = 1515  # 5:15 PM
min_meeting_time = 105  # 1.75 hours
travel_time_presidio_to_union = 22  # 22 minutes
travel_time_union_to_presidio = 24  # 24 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Presidio to meet Andrew
y = Int('y')  # Time to leave Union Square to return to Presidio
z = Int('z')  # Time to meet Andrew

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Presidio at 9:00 AM
s.add(x + travel_time_presidio_to_union >= start_time_andrew)  # Travel to Union Square
s.add(x + travel_time_presidio_to_union + min_meeting_time <= end_time_andrew)  # Meet Andrew for at least 1.75 hours
s.add(z >= start_time_andrew)  # Meet Andrew
s.add(z <= end_time_andrew)  # Meet Andrew
s.add(y >= z)  # Leave Union Square after meeting Andrew
s.add(y + travel_time_union_to_presidio <= 20 * 60)  # Return to Presidio by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Presidio to meet Andrew:", result[x])
print("Time to leave Union Square to return to Presidio:", result[y])
print("Time to meet Andrew:", result[z])