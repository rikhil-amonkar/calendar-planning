from z3 import *

# Define the variables
start_time_kenneth = 2000  # 8:00 PM
end_time_kenneth = 2200  # 10:00 PM
min_meeting_time = 105  # 1.75 hours
travel_time_gg_to_financial = 26  # 26 minutes
travel_time_financial_to_gg = 23  # 23 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Golden Gate Park to meet Kenneth
y = Int('y')  # Time to leave Financial District to return to Golden Gate Park
z = Int('z')  # Time to meet Kenneth

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Golden Gate Park at 9:00 AM
s.add(x + travel_time_gg_to_financial >= start_time_kenneth)  # Travel to Financial District
s.add(x + travel_time_gg_to_financial + min_meeting_time <= end_time_kenneth)  # Meet Kenneth for at least 1.75 hours
s.add(z >= start_time_kenneth)  # Meet Kenneth
s.add(z <= end_time_kenneth)  # Meet Kenneth
s.add(y >= z)  # Leave Financial District after meeting Kenneth
s.add(y + travel_time_financial_to_gg <= 24 * 60)  # Return to Golden Gate Park by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Golden Gate Park to meet Kenneth:", result[x])
print("Time to leave Financial District to return to Golden Gate Park:", result[y])
print("Time to meet Kenneth:", result[z])