from z3 import *

# Define the variables
start_time_betty = 515  # 5:15 PM
end_time_betty = 1745  # 5:45 PM
min_meeting_time = 60  # 1 hour
travel_time_richmond_to_financial = 22  # 22 minutes
travel_time_financial_to_richmond = 21  # 21 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Richmond District to meet Betty
y = Int('y')  # Time to leave Financial District to return to Richmond District
z = Int('z')  # Time to meet Betty

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Richmond District at 9:00 AM
s.add(x + travel_time_richmond_to_financial >= start_time_betty)  # Travel to Financial District
s.add(x + travel_time_richmond_to_financial + min_meeting_time <= end_time_betty)  # Meet Betty for at least 1 hour
s.add(z >= start_time_betty)  # Meet Betty
s.add(z <= end_time_betty)  # Meet Betty
s.add(y >= z)  # Leave Financial District after meeting Betty
s.add(y + travel_time_financial_to_richmond <= 24 * 60)  # Return to Richmond District by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Richmond District to meet Betty:", result[x])
print("Time to leave Financial District to return to Richmond District:", result[y])
print("Time to meet Betty:", result[z])