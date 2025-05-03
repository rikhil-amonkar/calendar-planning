from z3 import *

# Define the variables
start_time_betty = 845  # 8:45 AM
end_time_betty = 1800  # 6:00 PM
min_meeting_time = 105  # 1.75 hours
travel_time_pacific_to_fisherman = 13  # 13 minutes
travel_time_fisherman_to_pacific = 12  # 12 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Pacific Heights to meet Betty
y = Int('y')  # Time to leave Fisherman's Wharf to return to Pacific Heights
z = Int('z')  # Time to meet Betty

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Pacific Heights at 9:00 AM
s.add(x + travel_time_pacific_to_fisherman >= start_time_betty)  # Travel to Fisherman's Wharf
s.add(x + travel_time_pacific_to_fisherman + min_meeting_time <= end_time_betty)  # Meet Betty for at least 1.75 hours
s.add(z >= start_time_betty)  # Meet Betty
s.add(z <= end_time_betty)  # Meet Betty
s.add(y >= z)  # Leave Fisherman's Wharf after meeting Betty
s.add(y + travel_time_fisherman_to_pacific <= 19 * 60)  # Return to Pacific Heights by 7:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Pacific Heights to meet Betty:", result[x])
print("Time to leave Fisherman's Wharf to return to Pacific Heights:", result[y])
print("Time to meet Betty:", result[z])