from z3 import *

# Define the variables
start_time_betty = 1845  # 6:45 PM
end_time_betty = 2200  # 10:00 PM
min_meeting_time = 75  # 1.25 hours
travel_time_presidio_to_north = 18  # 18 minutes
travel_time_north_to_presidio = 17  # 17 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Presidio to meet Betty
y = Int('y')  # Time to leave North Beach to return to Presidio
z = Int('z')  # Time to meet Betty

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Presidio at 9:00 AM
s.add(x + travel_time_presidio_to_north >= start_time_betty)  # Travel to North Beach
s.add(x + travel_time_presidio_to_north + min_meeting_time <= end_time_betty)  # Meet Betty for at least 1.25 hours
s.add(z >= start_time_betty)  # Meet Betty
s.add(z <= end_time_betty)  # Meet Betty
s.add(y >= z)  # Leave North Beach after meeting Betty
s.add(y + travel_time_north_to_presidio <= 24 * 60)  # Return to Presidio by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Presidio to meet Betty:", result[x])
print("Time to leave North Beach to return to Presidio:", result[y])
print("Time to meet Betty:", result[z])