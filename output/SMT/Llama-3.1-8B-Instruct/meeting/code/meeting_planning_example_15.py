from z3 import *

# Define the variables
start_time_john = 1300  # 1:00 PM
end_time_john = 1815  # 6:15 PM
min_meeting_time = 90  # 1.5 hours
travel_time_russian_to_gg = 21  # 21 minutes
travel_time_gg_to_russian = 19  # 19 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Russian Hill to meet John
y = Int('y')  # Time to leave Golden Gate Park to return to Russian Hill
z = Int('z')  # Time to meet John

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Russian Hill at 9:00 AM
s.add(x + travel_time_russian_to_gg >= start_time_john)  # Travel to Golden Gate Park
s.add(x + travel_time_russian_to_gg + min_meeting_time <= end_time_john)  # Meet John for at least 1.5 hours
s.add(z >= start_time_john)  # Meet John
s.add(z <= end_time_john)  # Meet John
s.add(y >= z)  # Leave Golden Gate Park after meeting John
s.add(y + travel_time_gg_to_russian <= 20 * 60)  # Return to Russian Hill by 8:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Russian Hill to meet John:", result[x])
print("Time to leave Golden Gate Park to return to Russian Hill:", result[y])
print("Time to meet John:", result[z])