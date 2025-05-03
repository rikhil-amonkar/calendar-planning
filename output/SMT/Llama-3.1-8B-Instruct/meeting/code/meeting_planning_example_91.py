from z3 import *

# Define the variables
start_time_daniel = 1900  # 7:00 PM
end_time_daniel = 1915  # 8:15 PM
min_meeting_time = 75  # 1.25 hours
travel_time_russian_to_richmond = 14  # 14 minutes
travel_time_richmond_to_russian = 13  # 13 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Russian Hill to meet Daniel
y = Int('y')  # Time to leave Richmond District to return to Russian Hill
z = Int('z')  # Time to meet Daniel

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Russian Hill at 9:00 AM
s.add(x + travel_time_russian_to_richmond >= start_time_daniel)  # Travel to Richmond District
s.add(x + travel_time_russian_to_richmond + min_meeting_time <= end_time_daniel)  # Meet Daniel for at least 1.25 hours
s.add(z >= start_time_daniel)  # Meet Daniel
s.add(z <= end_time_daniel)  # Meet Daniel
s.add(y >= z)  # Leave Richmond District after meeting Daniel
s.add(y + travel_time_richmond_to_russian <= 24 * 60)  # Return to Russian Hill by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Russian Hill to meet Daniel:", result[x])
print("Time to leave Richmond District to return to Russian Hill:", result[y])
print("Time to meet Daniel:", result[z])