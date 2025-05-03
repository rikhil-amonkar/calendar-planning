from z3 import *

# Define the variables
start_time_paul = 0  # 9:30 AM
end_time_paul = 715  # 11:15 AM
min_meeting_time = 15  # 15 minutes
travel_time_richmond_to_nob = 17  # 17 minutes
travel_time_nob_to_richmond = 14  # 14 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Richmond District to meet Paul
y = Int('y')  # Time to leave Nob Hill to return to Richmond District
z = Int('z')  # Time to meet Paul

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Richmond District at 9:00 AM
s.add(x + travel_time_richmond_to_nob >= start_time_paul)  # Travel to Nob Hill
s.add(x + travel_time_richmond_to_nob + min_meeting_time <= end_time_paul)  # Meet Paul for at least 15 minutes
s.add(z >= start_time_paul)  # Meet Paul
s.add(z <= end_time_paul)  # Meet Paul
s.add(y >= z)  # Leave Nob Hill after meeting Paul
s.add(y + travel_time_nob_to_richmond <= 11 * 60)  # Return to Richmond District by 11:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Richmond District to meet Paul:", result[x])
print("Time to leave Nob Hill to return to Richmond District:", result[y])
print("Time to meet Paul:", result[z])