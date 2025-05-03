from z3 import *

# Define the variables
start_time_stephanie = 1745  # 4:45 PM
end_time_stephanie = 2145  # 9:45 PM
min_meeting_time = 120  # 2 hours
travel_time_fisherman_to_nob = 11  # 11 minutes
travel_time_nob_to_fisherman = 11  # 11 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Fisherman's Wharf to meet Stephanie
y = Int('y')  # Time to leave Nob Hill to return to Fisherman's Wharf
z = Int('z')  # Time to meet Stephanie

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Fisherman's Wharf at 9:00 AM
s.add(x + travel_time_fisherman_to_nob >= start_time_stephanie)  # Travel to Nob Hill
s.add(x + travel_time_fisherman_to_nob + min_meeting_time <= end_time_stephanie)  # Meet Stephanie for at least 2 hours
s.add(z >= start_time_stephanie)  # Meet Stephanie
s.add(z <= end_time_stephanie)  # Meet Stephanie
s.add(y >= z)  # Leave Nob Hill after meeting Stephanie
s.add(y + travel_time_nob_to_fisherman <= 24 * 60)  # Return to Fisherman's Wharf by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Fisherman's Wharf to meet Stephanie:", result[x])
print("Time to leave Nob Hill to return to Fisherman's Wharf:", result[y])
print("Time to meet Stephanie:", result[z])