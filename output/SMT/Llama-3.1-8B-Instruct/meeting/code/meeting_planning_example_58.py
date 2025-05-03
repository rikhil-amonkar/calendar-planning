from z3 import *

# Define the variables
start_time_nancy = 915  # 9:15 AM
end_time_nancy = 1745  # 4:45 PM
min_meeting_time = 30  # 30 minutes
travel_time_castro_to_financial = 20  # 20 minutes
travel_time_financial_to_castro = 23  # 23 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave The Castro to meet Nancy
y = Int('y')  # Time to leave Financial District to return to The Castro
z = Int('z')  # Time to meet Nancy

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at The Castro at 9:00 AM
s.add(x + travel_time_castro_to_financial >= start_time_nancy)  # Travel to Financial District
s.add(x + travel_time_castro_to_financial + min_meeting_time <= end_time_nancy)  # Meet Nancy for at least 30 minutes
s.add(z >= start_time_nancy)  # Meet Nancy
s.add(z <= end_time_nancy)  # Meet Nancy
s.add(y >= z)  # Leave Financial District after meeting Nancy
s.add(y + travel_time_financial_to_castro <= 19 * 60)  # Return to The Castro by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave The Castro to meet Nancy:", result[x])
print("Time to leave Financial District to return to The Castro:", result[y])
print("Time to meet Nancy:", result[z])