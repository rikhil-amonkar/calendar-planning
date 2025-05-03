from z3 import *

# Define the variables
start_time_matthew = 1100  # 11:00 AM
end_time_matthew = 1315  # 1:15 PM
min_meeting_time = 30  # 30 minutes
travel_time_nob_to_presidio = 17  # 17 minutes
travel_time_presidio_to_nob = 18  # 18 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Nob Hill to meet Matthew
y = Int('y')  # Time to leave Presidio to return to Nob Hill
z = Int('z')  # Time to meet Matthew

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Nob Hill at 9:00 AM
s.add(x + travel_time_nob_to_presidio >= start_time_matthew)  # Travel to Presidio
s.add(x + travel_time_nob_to_presidio + min_meeting_time <= end_time_matthew)  # Meet Matthew for at least 30 minutes
s.add(z >= start_time_matthew)  # Meet Matthew
s.add(z <= end_time_matthew)  # Meet Matthew
s.add(y >= z)  # Leave Presidio after meeting Matthew
s.add(y + travel_time_presidio_to_nob <= 14 * 60)  # Return to Nob Hill by 2:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Nob Hill to meet Matthew:", result[x])
print("Time to leave Presidio to return to Nob Hill:", result[y])
print("Time to meet Matthew:", result[z])