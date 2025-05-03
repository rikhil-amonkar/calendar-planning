from z3 import *

# Define the variables
start_time_james = 1015  # 10:15 AM
end_time_james = 1330  # 1:30 PM
min_meeting_time = 15  # 15 minutes
travel_time_gg_to_marina = 16  # 16 minutes
travel_time_marina_to_gg = 18  # 18 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Golden Gate Park to meet James
y = Int('y')  # Time to leave Marina District to return to Golden Gate Park
z = Int('z')  # Time to meet James

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Golden Gate Park at 9:00 AM
s.add(x + travel_time_gg_to_marina >= start_time_james)  # Travel to Marina District
s.add(x + travel_time_gg_to_marina + min_meeting_time <= end_time_james)  # Meet James for at least 15 minutes
s.add(z >= start_time_james)  # Meet James
s.add(z <= end_time_james)  # Meet James
s.add(y >= z)  # Leave Marina District after meeting James
s.add(y + travel_time_marina_to_gg <= 13 * 60)  # Return to Golden Gate Park by 1:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Golden Gate Park to meet James:", result[x])
print("Time to leave Marina District to return to Golden Gate Park:", result[y])
print("Time to meet James:", result[z])