from z3 import *

# Define the variables
start_time_paul = 1330  # 1:30 PM
end_time_paul = 1845  # 7:45 PM
min_meeting_time = 45  # 45 minutes
travel_time_north_to_bayview = 22  # 22 minutes
travel_time_bayview_to_north = 21  # 21 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave North Beach to meet Paul
y = Int('y')  # Time to leave Bayview to return to North Beach
z = Int('z')  # Time to meet Paul

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at North Beach at 9:00 AM
s.add(x + travel_time_north_to_bayview >= start_time_paul)  # Travel to Bayview
s.add(x + travel_time_north_to_bayview + min_meeting_time <= end_time_paul)  # Meet Paul for at least 45 minutes
s.add(z >= start_time_paul)  # Meet Paul
s.add(z <= end_time_paul)  # Meet Paul
s.add(y >= z)  # Leave Bayview after meeting Paul
s.add(y + travel_time_bayview_to_north <= 22 * 60)  # Return to North Beach by 8:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave North Beach to meet Paul:", result[x])
print("Time to leave Bayview to return to North Beach:", result[y])
print("Time to meet Paul:", result[z])