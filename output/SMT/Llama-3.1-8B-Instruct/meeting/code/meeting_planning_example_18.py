from z3 import *

# Define the variables
start_time_betty = 2030  # 8:30 PM
end_time_betty = 2200  # 10:00 PM
min_meeting_time = 75  # 1.25 hours
travel_time_marina_to_richmond = 11  # 11 minutes
travel_time_richmond_to_marina = 9  # 9 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Marina District to meet Betty
y = Int('y')  # Time to leave Richmond District to return to Marina District
z = Int('z')  # Time to meet Betty

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Marina District at 9:00 AM
s.add(x + travel_time_marina_to_richmond >= start_time_betty)  # Travel to Richmond District
s.add(x + travel_time_marina_to_richmond + min_meeting_time <= end_time_betty)  # Meet Betty for at least 1.25 hours
s.add(z >= start_time_betty)  # Meet Betty
s.add(z <= end_time_betty)  # Meet Betty
s.add(y >= z)  # Leave Richmond District after meeting Betty
s.add(y + travel_time_richmond_to_marina <= 24 * 60)  # Return to Marina District by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Marina District to meet Betty:", result[x])
print("Time to leave Richmond District to return to Marina District:", result[y])
print("Time to meet Betty:", result[z])