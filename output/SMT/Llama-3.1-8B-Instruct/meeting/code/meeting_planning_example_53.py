from z3 import *

# Define the variables
start_time_ashley = 615  # 10:15 AM
end_time_ashley = 1200  # 1:00 PM
min_meeting_time = 120  # 2 hours
travel_time_richmond_to_alamo = 13  # 13 minutes
travel_time_alamo_to_richmond = 12  # 12 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Richmond District to meet Ashley
y = Int('y')  # Time to leave Alamo Square to return to Richmond District
z = Int('z')  # Time to meet Ashley

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Richmond District at 9:00 AM
s.add(x + travel_time_richmond_to_alamo >= start_time_ashley)  # Travel to Alamo Square
s.add(x + travel_time_richmond_to_alamo + min_meeting_time <= end_time_ashley)  # Meet Ashley for at least 2 hours
s.add(z >= start_time_ashley)  # Meet Ashley
s.add(z <= end_time_ashley)  # Meet Ashley
s.add(y >= z)  # Leave Alamo Square after meeting Ashley
s.add(y + travel_time_alamo_to_richmond <= 13 * 60)  # Return to Richmond District by 1:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Richmond District to meet Ashley:", result[x])
print("Time to leave Alamo Square to return to Richmond District:", result[y])
print("Time to meet Ashley:", result[z])