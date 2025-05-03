from z3 import *

# Define the variables
start_time_robert = 1115  # 11:15 AM
end_time_robert = 1745  # 5:45 PM
min_meeting_time = 120  # 2 hours
travel_time_nob_to_presidio = 17  # 17 minutes
travel_time_presidio_to_nob = 18  # 18 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Nob Hill to meet Robert
y = Int('y')  # Time to leave Presidio to return to Nob Hill
z = Int('z')  # Time to meet Robert

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Nob Hill at 9:00 AM
s.add(x + travel_time_nob_to_presidio >= start_time_robert)  # Travel to Presidio
s.add(x + travel_time_nob_to_presidio + min_meeting_time <= end_time_robert)  # Meet Robert for at least 2 hours
s.add(z >= start_time_robert)  # Meet Robert
s.add(z <= end_time_robert)  # Meet Robert
s.add(y >= z)  # Leave Presidio after meeting Robert
s.add(y + travel_time_presidio_to_nob <= 20 * 60)  # Return to Nob Hill by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Nob Hill to meet Robert:", result[x])
print("Time to leave Presidio to return to Nob Hill:", result[y])
print("Time to meet Robert:", result[z])