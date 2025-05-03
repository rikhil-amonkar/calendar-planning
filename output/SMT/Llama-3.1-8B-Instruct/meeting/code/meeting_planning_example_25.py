from z3 import *

# Define the variables
start_time_david = 1600  # 4:00 PM
end_time_david = 2145  # 9:45 PM
min_meeting_time = 105  # 1.75 hours
travel_time_gg_to_chinatown = 23  # 23 minutes
travel_time_chinatown_to_gg = 23  # 23 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Golden Gate Park to meet David
y = Int('y')  # Time to leave Chinatown to return to Golden Gate Park
z = Int('z')  # Time to meet David

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Golden Gate Park at 9:00 AM
s.add(x + travel_time_gg_to_chinatown >= start_time_david)  # Travel to Chinatown
s.add(x + travel_time_gg_to_chinatown + min_meeting_time <= end_time_david)  # Meet David for at least 1.75 hours
s.add(z >= start_time_david)  # Meet David
s.add(z <= end_time_david)  # Meet David
s.add(y >= z)  # Leave Chinatown after meeting David
s.add(y + travel_time_chinatown_to_gg <= 24 * 60)  # Return to Golden Gate Park by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Golden Gate Park to meet David:", result[x])
print("Time to leave Chinatown to return to Golden Gate Park:", result[y])
print("Time to meet David:", result[z])