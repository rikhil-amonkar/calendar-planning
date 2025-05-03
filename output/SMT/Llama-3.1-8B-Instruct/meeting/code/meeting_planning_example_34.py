from z3 import *

# Define the variables
start_time_thomas = 1215  # 12:15 PM
end_time_thomas = 1515  # 5:15 PM
min_meeting_time = 105  # 1.75 hours
travel_time_bayview_to_pacific = 23  # 23 minutes
travel_time_pacific_to_bayview = 22  # 22 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Bayview to meet Thomas
y = Int('y')  # Time to leave Pacific Heights to return to Bayview
z = Int('z')  # Time to meet Thomas

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Bayview at 9:00 AM
s.add(x + travel_time_bayview_to_pacific >= start_time_thomas)  # Travel to Pacific Heights
s.add(x + travel_time_bayview_to_pacific + min_meeting_time <= end_time_thomas)  # Meet Thomas for at least 1.75 hours
s.add(z >= start_time_thomas)  # Meet Thomas
s.add(z <= end_time_thomas)  # Meet Thomas
s.add(y >= z)  # Leave Pacific Heights after meeting Thomas
s.add(y + travel_time_pacific_to_bayview <= 19 * 60)  # Return to Bayview by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Bayview to meet Thomas:", result[x])
print("Time to leave Pacific Heights to return to Bayview:", result[y])
print("Time to meet Thomas:", result[z])