from z3 import *

# Define the variables
start_time_betty = 1230  # 12:30 PM
end_time_betty = 1715  # 7:15 PM
min_meeting_time = 75  # 1.25 hours
travel_time_richmond_to_alamo = 13  # 13 minutes
travel_time_alamo_to_richmond = 12  # 12 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Richmond District to meet Betty
y = Int('y')  # Time to leave Alamo Square to return to Richmond District
z = Int('z')  # Time to meet Betty

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Richmond District at 9:00 AM
s.add(x + travel_time_richmond_to_alamo >= start_time_betty)  # Travel to Alamo Square
s.add(x + travel_time_richmond_to_alamo + min_meeting_time <= end_time_betty)  # Meet Betty for at least 1.25 hours
s.add(z >= start_time_betty)  # Meet Betty
s.add(z <= end_time_betty)  # Meet Betty
s.add(y >= z)  # Leave Alamo Square after meeting Betty
s.add(y + travel_time_alamo_to_richmond <= 22 * 60)  # Return to Richmond District by 8:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Richmond District to meet Betty:", result[x])
print("Time to leave Alamo Square to return to Richmond District:", result[y])
print("Time to meet Betty:", result[z])