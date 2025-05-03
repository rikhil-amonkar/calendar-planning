from z3 import *

# Define the variables
start_time_william = 1215  # 12:15 PM
end_time_william = 2200  # 10:00 PM
min_meeting_time = 75  # 1.25 hours
travel_time_nob_to_castro = 17  # 17 minutes
travel_time_castro_to_nob = 16  # 16 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Nob Hill to meet William
y = Int('y')  # Time to leave The Castro to return to Nob Hill
z = Int('z')  # Time to meet William

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Nob Hill at 9:00 AM
s.add(x + travel_time_nob_to_castro >= start_time_william)  # Travel to The Castro
s.add(x + travel_time_nob_to_castro + min_meeting_time <= end_time_william)  # Meet William for at least 1.25 hours
s.add(z >= start_time_william)  # Meet William
s.add(z <= end_time_william)  # Meet William
s.add(y >= z)  # Leave The Castro after meeting William
s.add(y + travel_time_castro_to_nob <= 23 * 60)  # Return to Nob Hill by 11:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Nob Hill to meet William:", result[x])
print("Time to leave The Castro to return to Nob Hill:", result[y])
print("Time to meet William:", result[z])