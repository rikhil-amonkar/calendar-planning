from z3 import *

# Define the variables
start_time_stephanie = 2015  # 7:15 PM
end_time_stephanie = 2200  # 10:00 PM
min_meeting_time = 90  # 1.5 hours
travel_time_gg_to_presidio = 11  # 11 minutes
travel_time_presidio_to_gg = 12  # 12 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Golden Gate Park to meet Stephanie
y = Int('y')  # Time to leave Presidio to return to Golden Gate Park
z = Int('z')  # Time to meet Stephanie

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Golden Gate Park at 9:00 AM
s.add(x + travel_time_gg_to_presidio >= start_time_stephanie)  # Travel to Presidio
s.add(x + travel_time_gg_to_presidio + min_meeting_time <= end_time_stephanie)  # Meet Stephanie for at least 1.5 hours
s.add(z >= start_time_stephanie)  # Meet Stephanie
s.add(z <= end_time_stephanie)  # Meet Stephanie
s.add(y >= z)  # Leave Presidio after meeting Stephanie
s.add(y + travel_time_presidio_to_gg <= 24 * 60)  # Return to Golden Gate Park by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Golden Gate Park to meet Stephanie:", result[x])
print("Time to leave Presidio to return to Golden Gate Park:", result[y])
print("Time to meet Stephanie:", result[z])