from z3 import *

# Define the variables
start_time_stephanie = 0  # 8:00 AM
end_time_stephanie = 1800  # 3:00 PM
min_meeting_time = 105  # 1.75 hours
travel_time_chinatown_to_marina = 12  # 12 minutes
travel_time_marina_to_chinatown = 16  # 16 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Chinatown to meet Stephanie
y = Int('y')  # Time to leave Marina District to return to Chinatown
z = Int('z')  # Time to meet Stephanie

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Chinatown at 9:00 AM
s.add(x + travel_time_chinatown_to_marina >= start_time_stephanie)  # Travel to Marina District
s.add(x + travel_time_chinatown_to_marina + min_meeting_time <= end_time_stephanie)  # Meet Stephanie for at least 1.75 hours
s.add(z >= start_time_stephanie)  # Meet Stephanie
s.add(z <= end_time_stephanie)  # Meet Stephanie
s.add(y >= z)  # Leave Marina District after meeting Stephanie
s.add(y + travel_time_marina_to_chinatown <= 18 * 60)  # Return to Chinatown by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Chinatown to meet Stephanie:", result[x])
print("Time to leave Marina District to return to Chinatown:", result[y])
print("Time to meet Stephanie:", result[z])