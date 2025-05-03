from z3 import *

# Define the variables
start_time_joshua = 1130  # 11:30 AM
end_time_joshua = 2200  # 10:00 PM
min_meeting_time = 75  # 1.25 hours
travel_time_mission_to_haight = 12  # 12 minutes
travel_time_haight_to_mission = 11  # 11 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Mission District to meet Joshua
y = Int('y')  # Time to leave Haight-Ashbury to return to Mission District
z = Int('z')  # Time to meet Joshua

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Mission District at 9:00 AM
s.add(x + travel_time_mission_to_haight >= start_time_joshua)  # Travel to Haight-Ashbury
s.add(x + travel_time_mission_to_haight + min_meeting_time <= end_time_joshua)  # Meet Joshua for at least 1.25 hours
s.add(z >= start_time_joshua)  # Meet Joshua
s.add(z <= end_time_joshua)  # Meet Joshua
s.add(y >= z)  # Leave Haight-Ashbury after meeting Joshua
s.add(y + travel_time_haight_to_mission <= 24 * 60)  # Return to Mission District by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Mission District to meet Joshua:", result[x])
print("Time to leave Haight-Ashbury to return to Mission District:", result[y])
print("Time to meet Joshua:", result[z])