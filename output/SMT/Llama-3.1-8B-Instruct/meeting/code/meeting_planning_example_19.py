from z3 import *

# Define the variables
start_time_john = 1945  # 7:45 PM
end_time_john = 2045  # 8:45 PM
min_meeting_time = 45  # 45 minutes
travel_time_gg_to_pacific = 16  # 16 minutes
travel_time_pacific_to_gg = 15  # 15 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Golden Gate Park to meet John
y = Int('y')  # Time to leave Pacific Heights to return to Golden Gate Park
z = Int('z')  # Time to meet John

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Golden Gate Park at 9:00 AM
s.add(x + travel_time_gg_to_pacific >= start_time_john)  # Travel to Pacific Heights
s.add(x + travel_time_gg_to_pacific + min_meeting_time <= end_time_john)  # Meet John for at least 45 minutes
s.add(z >= start_time_john)  # Meet John
s.add(z <= end_time_john)  # Meet John
s.add(y >= z)  # Leave Pacific Heights after meeting John
s.add(y + travel_time_pacific_to_gg <= 23 * 60)  # Return to Golden Gate Park by 11:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Golden Gate Park to meet John:", result[x])
print("Time to leave Pacific Heights to return to Golden Gate Park:", result[y])
print("Time to meet John:", result[z])