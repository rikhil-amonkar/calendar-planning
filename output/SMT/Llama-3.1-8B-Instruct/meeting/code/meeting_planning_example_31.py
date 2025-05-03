from z3 import *

# Define the variables
start_time_anthony = 715  # 7:15 AM
end_time_anthony = 1200  # 12:00 PM
min_meeting_time = 15  # 15 minutes
travel_time_nob_to_alamo = 11  # 11 minutes
travel_time_alamo_to_nob = 11  # 11 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Nob Hill to meet Anthony
y = Int('y')  # Time to leave Alamo Square to return to Nob Hill
z = Int('z')  # Time to meet Anthony

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Nob Hill at 9:00 AM
s.add(x + travel_time_nob_to_alamo >= start_time_anthony)  # Travel to Alamo Square
s.add(x + travel_time_nob_to_alamo + min_meeting_time <= end_time_anthony)  # Meet Anthony for at least 15 minutes
s.add(z >= start_time_anthony)  # Meet Anthony
s.add(z <= end_time_anthony)  # Meet Anthony
s.add(y >= z)  # Leave Alamo Square after meeting Anthony
s.add(y + travel_time_alamo_to_nob <= 11 * 60)  # Return to Nob Hill by 11:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Nob Hill to meet Anthony:", result[x])
print("Time to leave Alamo Square to return to Nob Hill:", result[y])
print("Time to meet Anthony:", result[z])