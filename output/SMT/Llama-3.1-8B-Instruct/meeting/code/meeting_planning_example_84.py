from z3 import *

# Define the variables
start_time_thomas = 1100  # 11:00 AM
end_time_thomas = 1200  # 1:00 PM
min_meeting_time = 30  # 30 minutes
travel_time_alamo_to_haight = 5  # 5 minutes
travel_time_haight_to_alamo = 5  # 5 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Alamo Square to meet Thomas
y = Int('y')  # Time to leave Haight-Ashbury to return to Alamo Square
z = Int('z')  # Time to meet Thomas

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Alamo Square at 9:00 AM
s.add(x + travel_time_alamo_to_haight >= start_time_thomas)  # Travel to Haight-Ashbury
s.add(x + travel_time_alamo_to_haight + min_meeting_time <= end_time_thomas)  # Meet Thomas for at least 30 minutes
s.add(z >= start_time_thomas)  # Meet Thomas
s.add(z <= end_time_thomas)  # Meet Thomas
s.add(y >= z)  # Leave Haight-Ashbury after meeting Thomas
s.add(y + travel_time_haight_to_alamo <= 12 * 60)  # Return to Alamo Square by 12:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Alamo Square to meet Thomas:", result[x])
print("Time to leave Haight-Ashbury to return to Alamo Square:", result[y])
print("Time to meet Thomas:", result[z])