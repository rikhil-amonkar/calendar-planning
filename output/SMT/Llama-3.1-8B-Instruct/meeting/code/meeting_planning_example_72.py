from z3 import *

# Define the variables
start_time_john = 0  # 9:45 AM
end_time_john = 1530  # 2:30 PM
min_meeting_time = 90  # 1.5 hours
travel_time_pacific_to_alamo = 10  # 10 minutes
travel_time_alamo_to_pacific = 10  # 10 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Pacific Heights to meet John
y = Int('y')  # Time to leave Alamo Square to return to Pacific Heights
z = Int('z')  # Time to meet John

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Pacific Heights at 9:00 AM
s.add(x + travel_time_pacific_to_alamo >= start_time_john)  # Travel to Alamo Square
s.add(x + travel_time_pacific_to_alamo + min_meeting_time <= end_time_john)  # Meet John for at least 1.5 hours
s.add(z >= start_time_john)  # Meet John
s.add(z <= end_time_john)  # Meet John
s.add(y >= z)  # Leave Alamo Square after meeting John
s.add(y + travel_time_alamo_to_pacific <= 14 * 60)  # Return to Pacific Heights by 2:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Pacific Heights to meet John:", result[x])
print("Time to leave Alamo Square to return to Pacific Heights:", result[y])
print("Time to meet John:", result[z])