from z3 import *

# Define the variables
start_time_carol = 1400  # 2:00 PM
end_time_carol = 1830  # 6:30 PM
min_meeting_time = 75  # 1.25 hours
travel_time_nob_to_sun = 25  # 25 minutes
travel_time_sun_to_nob = 27  # 27 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Nob Hill to meet Carol
y = Int('y')  # Time to leave Sunset District to return to Nob Hill
z = Int('z')  # Time to meet Carol

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Nob Hill at 9:00 AM
s.add(x + travel_time_nob_to_sun >= start_time_carol)  # Travel to Sunset District
s.add(x + travel_time_nob_to_sun + min_meeting_time <= end_time_carol)  # Meet Carol for at least 1.25 hours
s.add(z >= start_time_carol)  # Meet Carol
s.add(z <= end_time_carol)  # Meet Carol
s.add(y >= z)  # Leave Sunset District after meeting Carol
s.add(y + travel_time_sun_to_nob <= 22 * 60)  # Return to Nob Hill by 8:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Nob Hill to meet Carol:", result[x])
print("Time to leave Sunset District to return to Nob Hill:", result[y])
print("Time to meet Carol:", result[z])