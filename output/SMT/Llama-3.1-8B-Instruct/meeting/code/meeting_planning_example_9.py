from z3 import *

# Define the variables
start_time_mary = 1200  # 12:00 PM
end_time_mary = 1415  # 2:15 PM
min_meeting_time = 75  # 1.25 hours
travel_time_union_to_nob = 9  # 9 minutes
travel_time_nob_to_union = 7  # 7 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Union Square to meet Mary
y = Int('y')  # Time to leave Nob Hill to return to Union Square
z = Int('z')  # Time to meet Mary

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Union Square at 9:00 AM
s.add(x + travel_time_union_to_nob >= start_time_mary)  # Travel to Nob Hill
s.add(x + travel_time_union_to_nob + min_meeting_time <= end_time_mary)  # Meet Mary for at least 1.25 hours
s.add(z >= start_time_mary)  # Meet Mary
s.add(z <= end_time_mary)  # Meet Mary
s.add(y >= z)  # Leave Nob Hill after meeting Mary
s.add(y + travel_time_nob_to_union <= 14 * 60)  # Return to Union Square by 2:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Union Square to meet Mary:", result[x])
print("Time to leave Nob Hill to return to Union Square:", result[y])
print("Time to meet Mary:", result[z])