from z3 import *

# Define the variables
start_time_paul = 1100  # 11:00 AM
end_time_paul = 1430  # 4:30 PM
min_meeting_time = 90  # 1.5 hours
travel_time_haight_to_bayview = 18  # 18 minutes
travel_time_bayview_to_haight = 19  # 19 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Haight-Ashbury to meet Paul
y = Int('y')  # Time to leave Bayview to return to Haight-Ashbury
z = Int('z')  # Time to meet Paul

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Haight-Ashbury at 9:00 AM
s.add(x + travel_time_haight_to_bayview >= start_time_paul)  # Travel to Bayview
s.add(x + travel_time_haight_to_bayview + min_meeting_time <= end_time_paul)  # Meet Paul for at least 1.5 hours
s.add(z >= start_time_paul)  # Meet Paul
s.add(z <= end_time_paul)  # Meet Paul
s.add(y >= z)  # Leave Bayview after meeting Paul
s.add(y + travel_time_bayview_to_haight <= 19 * 60)  # Return to Haight-Ashbury by 5:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Haight-Ashbury to meet Paul:", result[x])
print("Time to leave Bayview to return to Haight-Ashbury:", result[y])
print("Time to meet Paul:", result[z])