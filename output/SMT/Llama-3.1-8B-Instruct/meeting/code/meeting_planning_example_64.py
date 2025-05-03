from z3 import *

# Define the variables
start_time_margaret = 1445  # 3:45 PM
end_time_margaret = 1715  # 7:15 PM
min_meeting_time = 45  # 45 minutes
travel_time_nob_to_pacific = 8  # 8 minutes
travel_time_pacific_to_nob = 8  # 8 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Nob Hill to meet Margaret
y = Int('y')  # Time to leave Pacific Heights to return to Nob Hill
z = Int('z')  # Time to meet Margaret

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Nob Hill at 9:00 AM
s.add(x + travel_time_nob_to_pacific >= start_time_margaret)  # Travel to Pacific Heights
s.add(x + travel_time_nob_to_pacific + min_meeting_time <= end_time_margaret)  # Meet Margaret for at least 45 minutes
s.add(z >= start_time_margaret)  # Meet Margaret
s.add(z <= end_time_margaret)  # Meet Margaret
s.add(y >= z)  # Leave Pacific Heights after meeting Margaret
s.add(y + travel_time_pacific_to_nob <= 21 * 60)  # Return to Nob Hill by 7:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Nob Hill to meet Margaret:", result[x])
print("Time to leave Pacific Heights to return to Nob Hill:", result[y])
print("Time to meet Margaret:", result[z])