from z3 import *

# Define the variables
start_time_sandra = 1900  # 7:00 PM
end_time_sandra = 2100  # 9:00 PM
min_meeting_time = 45  # 45 minutes
travel_time_gg_to_embarcadero = 25  # 25 minutes
travel_time_embarcadero_to_gg = 25  # 25 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Golden Gate Park to meet Sandra
y = Int('y')  # Time to leave Embarcadero to return to Golden Gate Park
z = Int('z')  # Time to meet Sandra

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Golden Gate Park at 9:00 AM
s.add(x + travel_time_gg_to_embarcadero >= start_time_sandra)  # Travel to Embarcadero
s.add(x + travel_time_gg_to_embarcadero + min_meeting_time <= end_time_sandra)  # Meet Sandra for at least 45 minutes
s.add(z >= start_time_sandra)  # Meet Sandra
s.add(z <= end_time_sandra)  # Meet Sandra
s.add(y >= z)  # Leave Embarcadero after meeting Sandra
s.add(y + travel_time_embarcadero_to_gg <= 24 * 60)  # Return to Golden Gate Park by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Golden Gate Park to meet Sandra:", result[x])
print("Time to leave Embarcadero to return to Golden Gate Park:", result[y])
print("Time to meet Sandra:", result[z])