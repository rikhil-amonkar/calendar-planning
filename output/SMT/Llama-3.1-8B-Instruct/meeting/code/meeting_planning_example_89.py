from z3 import *

# Define the variables
start_time_patricia = 1800  # 6:00 PM
end_time_patricia = 1830  # 7:30 PM
min_meeting_time = 60  # 1 hour
travel_time_mission_to_bayview = 15  # 15 minutes
travel_time_bayview_to_mission = 13  # 13 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Mission District to meet Patricia
y = Int('y')  # Time to leave Bayview to return to Mission District
z = Int('z')  # Time to meet Patricia

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Mission District at 9:00 AM
s.add(x + travel_time_mission_to_bayview >= start_time_patricia)  # Travel to Bayview
s.add(x + travel_time_mission_to_bayview + min_meeting_time <= end_time_patricia)  # Meet Patricia for at least 1 hour
s.add(z >= start_time_patricia)  # Meet Patricia
s.add(z <= end_time_patricia)  # Meet Patricia
s.add(y >= z)  # Leave Bayview after meeting Patricia
s.add(y + travel_time_bayview_to_mission <= 24 * 60)  # Return to Mission District by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Mission District to meet Patricia:", result[x])
print("Time to leave Bayview to return to Mission District:", result[y])
print("Time to meet Patricia:", result[z])