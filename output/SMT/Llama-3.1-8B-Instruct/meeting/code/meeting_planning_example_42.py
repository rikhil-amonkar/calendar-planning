from z3 import *

# Define the variables
start_time_timothy = 1300  # 1:00 PM
end_time_timothy = 1900  # 7:00 PM
min_meeting_time = 30  # 30 minutes
travel_time_nob_to_presidio = 17  # 17 minutes
travel_time_presidio_to_nob = 18  # 18 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Nob Hill to meet Timothy
y = Int('y')  # Time to leave Presidio to return to Nob Hill
z = Int('z')  # Time to meet Timothy

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Nob Hill at 9:00 AM
s.add(x + travel_time_nob_to_presidio >= start_time_timothy)  # Travel to Presidio
s.add(x + travel_time_nob_to_presidio + min_meeting_time <= end_time_timothy)  # Meet Timothy for at least 30 minutes
s.add(z >= start_time_timothy)  # Meet Timothy
s.add(z <= end_time_timothy)  # Meet Timothy
s.add(y >= z)  # Leave Presidio after meeting Timothy
s.add(y + travel_time_presidio_to_nob <= 21 * 60)  # Return to Nob Hill by 8:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Nob Hill to meet Timothy:", result[x])
print("Time to leave Presidio to return to Nob Hill:", result[y])
print("Time to meet Timothy:", result[z])