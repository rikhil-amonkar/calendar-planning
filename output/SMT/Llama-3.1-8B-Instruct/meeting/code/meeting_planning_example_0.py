from z3 import *

# Define the variables
start_time_stephanie = 930  # 10:30 AM
end_time_stephanie = 1130  # 11:30 AM
min_meeting_time = 120  # 2 hours
travel_time_marina_to_mission = 20  # 20 minutes
travel_time_mission_to_marina = 19  # 19 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Marina District to meet Stephanie
y = Int('y')  # Time to leave Mission District to return to Marina District

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Marina District at 9:00 AM
s.add(x + travel_time_marina_to_mission >= start_time_stephanie)  # Travel to Mission District
s.add(x + travel_time_marina_to_mission + min_meeting_time <= end_time_stephanie)  # Meet Stephanie for at least 2 hours
s.add(y >= start_time_stephanie)  # Leave Mission District after meeting Stephanie
s.add(y + travel_time_mission_to_marina <= 18 * 60)  # Return to Marina District by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Marina District to meet Stephanie:", result[x])
print("Time to leave Mission District to return to Marina District:", result[y])