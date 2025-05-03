from z3 import *

# Define the variables
start_time_joshua = 2045  # 8:45 PM
end_time_joshua = 2145  # 9:45 PM
min_meeting_time = 15  # 15 minutes
travel_time_sunset_to_gg = 11  # 11 minutes
travel_time_gg_to_sunset = 10  # 10 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Sunset District to meet Joshua
y = Int('y')  # Time to leave Golden Gate Park to return to Sunset District
z = Int('z')  # Time to meet Joshua

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Sunset District at 9:00 AM
s.add(x + travel_time_sunset_to_gg >= start_time_joshua)  # Travel to Golden Gate Park
s.add(x + travel_time_sunset_to_gg + min_meeting_time <= end_time_joshua)  # Meet Joshua for at least 15 minutes
s.add(z >= start_time_joshua)  # Meet Joshua
s.add(z <= end_time_joshua)  # Meet Joshua
s.add(y >= z)  # Leave Golden Gate Park after meeting Joshua
s.add(y + travel_time_gg_to_sunset <= 24 * 60)  # Return to Sunset District by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Sunset District to meet Joshua:", result[x])
print("Time to leave Golden Gate Park to return to Sunset District:", result[y])
print("Time to meet Joshua:", result[z])