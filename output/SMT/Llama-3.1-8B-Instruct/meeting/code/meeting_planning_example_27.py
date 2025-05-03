from z3 import *

# Define the variables
start_time_margaret = 1900  # 7:00 PM
end_time_margaret = 1945  # 7:45 PM
min_meeting_time = 15  # 15 minutes
travel_time_marina_to_pacific = 7  # 7 minutes
travel_time_pacific_to_marina = 6  # 6 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Marina District to meet Margaret
y = Int('y')  # Time to leave Pacific Heights to return to Marina District
z = Int('z')  # Time to meet Margaret

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Marina District at 9:00 AM
s.add(x + travel_time_marina_to_pacific >= start_time_margaret)  # Travel to Pacific Heights
s.add(x + travel_time_marina_to_pacific + min_meeting_time <= end_time_margaret)  # Meet Margaret for at least 15 minutes
s.add(z >= start_time_margaret)  # Meet Margaret
s.add(z <= end_time_margaret)  # Meet Margaret
s.add(y >= z)  # Leave Pacific Heights after meeting Margaret
s.add(y + travel_time_pacific_to_marina <= 23 * 60)  # Return to Marina District by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Marina District to meet Margaret:", result[x])
print("Time to leave Pacific Heights to return to Marina District:", result[y])
print("Time to meet Margaret:", result[z])