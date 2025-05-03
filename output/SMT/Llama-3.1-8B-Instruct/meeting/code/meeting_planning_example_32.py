from z3 import *

# Define the variables
start_time_jeffrey = 0  # 7:00 AM
end_time_jeffrey = 1530  # 5:30 PM
min_meeting_time = 105  # 1.75 hours
travel_time_castro_to_gg = 11  # 11 minutes
travel_time_gg_to_castro = 13  # 13 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave The Castro to meet Jeffrey
y = Int('y')  # Time to leave Golden Gate Park to return to The Castro
z = Int('z')  # Time to meet Jeffrey

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at The Castro at 9:00 AM
s.add(x + travel_time_castro_to_gg >= start_time_jeffrey)  # Travel to Golden Gate Park
s.add(x + travel_time_castro_to_gg + min_meeting_time <= end_time_jeffrey)  # Meet Jeffrey for at least 1.75 hours
s.add(z >= start_time_jeffrey)  # Meet Jeffrey
s.add(z <= end_time_jeffrey)  # Meet Jeffrey
s.add(y >= z)  # Leave Golden Gate Park after meeting Jeffrey
s.add(y + travel_time_gg_to_castro <= 19 * 60)  # Return to The Castro by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave The Castro to meet Jeffrey:", result[x])
print("Time to leave Golden Gate Park to return to The Castro:", result[y])
print("Time to meet Jeffrey:", result[z])