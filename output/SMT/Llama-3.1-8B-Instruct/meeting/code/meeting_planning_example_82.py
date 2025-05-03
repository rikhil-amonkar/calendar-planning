from z3 import *

# Define the variables
start_time_ashley = 1745  # 5:45 PM
end_time_ashley = 2130  # 9:30 PM
min_meeting_time = 75  # 1.25 hours
travel_time_gg_to_alamo = 10  # 10 minutes
travel_time_alamo_to_gg = 9  # 9 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Golden Gate Park to meet Ashley
y = Int('y')  # Time to leave Alamo Square to return to Golden Gate Park
z = Int('z')  # Time to meet Ashley

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Golden Gate Park at 9:00 AM
s.add(x + travel_time_gg_to_alamo >= start_time_ashley)  # Travel to Alamo Square
s.add(x + travel_time_gg_to_alamo + min_meeting_time <= end_time_ashley)  # Meet Ashley for at least 1.25 hours
s.add(z >= start_time_ashley)  # Meet Ashley
s.add(z <= end_time_ashley)  # Meet Ashley
s.add(y >= z)  # Leave Alamo Square after meeting Ashley
s.add(y + travel_time_alamo_to_gg <= 24 * 60)  # Return to Golden Gate Park by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Golden Gate Park to meet Ashley:", result[x])
print("Time to leave Alamo Square to return to Golden Gate Park:", result[y])
print("Time to meet Ashley:", result[z])