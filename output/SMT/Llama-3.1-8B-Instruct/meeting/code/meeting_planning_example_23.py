from z3 import *

# Define the variables
start_time_john = 1730  # 5:30 PM
end_time_john = 2100  # 9:00 PM
min_meeting_time = 75  # 1.25 hours
travel_time_bayview_to_russian = 23  # 23 minutes
travel_time_russian_to_bayview = 23  # 23 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Bayview to meet John
y = Int('y')  # Time to leave Russian Hill to return to Bayview
z = Int('z')  # Time to meet John

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Bayview at 9:00 AM
s.add(x + travel_time_bayview_to_russian >= start_time_john)  # Travel to Russian Hill
s.add(x + travel_time_bayview_to_russian + min_meeting_time <= end_time_john)  # Meet John for at least 1.25 hours
s.add(z >= start_time_john)  # Meet John
s.add(z <= end_time_john)  # Meet John
s.add(y >= z)  # Leave Russian Hill after meeting John
s.add(y + travel_time_russian_to_bayview <= 24 * 60)  # Return to Bayview by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Bayview to meet John:", result[x])
print("Time to leave Russian Hill to return to Bayview:", result[y])
print("Time to meet John:", result[z])