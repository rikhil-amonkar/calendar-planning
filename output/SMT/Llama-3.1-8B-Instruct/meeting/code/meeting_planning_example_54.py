from z3 import *

# Define the variables
start_time_william = 1315  # 1:15 PM
end_time_william = 1330  # 2:15 PM
min_meeting_time = 45  # 45 minutes
travel_time_financial_to_mission = 17  # 17 minutes
travel_time_mission_to_financial = 17  # 17 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Financial District to meet William
y = Int('y')  # Time to leave Mission District to return to Financial District
z = Int('z')  # Time to meet William

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Financial District at 9:00 AM
s.add(x + travel_time_financial_to_mission >= start_time_william)  # Travel to Mission District
s.add(x + travel_time_financial_to_mission + min_meeting_time <= end_time_william)  # Meet William for at least 45 minutes
s.add(z >= start_time_william)  # Meet William
s.add(z <= end_time_william)  # Meet William
s.add(y >= z)  # Leave Mission District after meeting William
s.add(y + travel_time_mission_to_financial <= 14 * 60)  # Return to Financial District by 2:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Financial District to meet William:", result[x])
print("Time to leave Mission District to return to Financial District:", result[y])
print("Time to meet William:", result[z])