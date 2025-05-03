from z3 import *

# Define the variables
start_time_daniel = 1845  # 7:45 PM
end_time_daniel = 2100  # 9:00 PM
min_meeting_time = 15  # 15 minutes
travel_time_marina_to_nob = 12  # 12 minutes
travel_time_nob_to_marina = 11  # 11 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Marina District to meet Daniel
y = Int('y')  # Time to leave Nob Hill to return to Marina District
z = Int('z')  # Time to meet Daniel

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Marina District at 9:00 AM
s.add(x + travel_time_marina_to_nob >= start_time_daniel)  # Travel to Nob Hill
s.add(x + travel_time_marina_to_nob + min_meeting_time <= end_time_daniel)  # Meet Daniel for at least 15 minutes
s.add(z >= start_time_daniel)  # Meet Daniel
s.add(z <= end_time_daniel)  # Meet Daniel
s.add(y >= z)  # Leave Nob Hill after meeting Daniel
s.add(y + travel_time_nob_to_marina <= 24 * 60)  # Return to Marina District by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Marina District to meet Daniel:", result[x])
print("Time to leave Nob Hill to return to Marina District:", result[y])
print("Time to meet Daniel:", result[z])