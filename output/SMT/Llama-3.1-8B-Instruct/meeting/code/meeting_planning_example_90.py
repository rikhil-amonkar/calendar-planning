from z3 import *

# Define the variables
start_time_laura = 0  # 8:15 AM
end_time_laura = 1745  # 6:45 PM
min_meeting_time = 15  # 15 minutes
travel_time_alamo_to_chinatown = 16  # 16 minutes
travel_time_chinatown_to_alamo = 17  # 17 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Alamo Square to meet Laura
y = Int('y')  # Time to leave Chinatown to return to Alamo Square
z = Int('z')  # Time to meet Laura

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Alamo Square at 9:00 AM
s.add(x + travel_time_alamo_to_chinatown >= start_time_laura)  # Travel to Chinatown
s.add(x + travel_time_alamo_to_chinatown + min_meeting_time <= end_time_laura)  # Meet Laura for at least 15 minutes
s.add(z >= start_time_laura)  # Meet Laura
s.add(z <= end_time_laura)  # Meet Laura
s.add(y >= z)  # Leave Chinatown after meeting Laura
s.add(y + travel_time_chinatown_to_alamo <= 21 * 60)  # Return to Alamo Square by 7:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Alamo Square to meet Laura:", result[x])
print("Time to leave Chinatown to return to Alamo Square:", result[y])
print("Time to meet Laura:", result[z])