from z3 import *

# Define the variables
start_time_mary = 2000  # 8:00 PM
end_time_mary = 2200  # 10:00 PM
min_meeting_time = 120  # 2 hours
travel_time_nob_to_marina = 11  # 11 minutes
travel_time_marina_to_nob = 12  # 12 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Nob Hill to meet Mary
y = Int('y')  # Time to leave Marina District to return to Nob Hill
z = Int('z')  # Time to meet Mary

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Nob Hill at 9:00 AM
s.add(x + travel_time_nob_to_marina >= start_time_mary)  # Travel to Marina District
s.add(x + travel_time_nob_to_marina + min_meeting_time <= end_time_mary)  # Meet Mary for at least 2 hours
s.add(z >= start_time_mary)  # Meet Mary
s.add(z <= end_time_mary)  # Meet Mary
s.add(y >= z)  # Leave Marina District after meeting Mary
s.add(y + travel_time_marina_to_nob <= 24 * 60)  # Return to Nob Hill by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Nob Hill to meet Mary:", result[x])
print("Time to leave Marina District to return to Nob Hill:", result[y])
print("Time to meet Mary:", result[z])