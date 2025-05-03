from z3 import *

# Define the variables
start_time_margaret = 0  # 8:00 AM
end_time_margaret = 1345  # 3:45 PM
min_meeting_time = 30  # 30 minutes
travel_time_mission_to_haight = 12  # 12 minutes
travel_time_haight_to_mission = 11  # 11 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Mission District to meet Margaret
y = Int('y')  # Time to leave Haight-Ashbury to return to Mission District
z = Int('z')  # Time to meet Margaret

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Mission District at 9:00 AM
s.add(x + travel_time_mission_to_haight >= start_time_margaret)  # Travel to Haight-Ashbury
s.add(x + travel_time_mission_to_haight + min_meeting_time <= end_time_margaret)  # Meet Margaret for at least 30 minutes
s.add(z >= start_time_margaret)  # Meet Margaret
s.add(z <= end_time_margaret)  # Meet Margaret
s.add(y >= z)  # Leave Haight-Ashbury after meeting Margaret
s.add(y + travel_time_haight_to_mission <= 18 * 60)  # Return to Mission District by 4:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Mission District to meet Margaret:", result[x])
print("Time to leave Haight-Ashbury to return to Mission District:", result[y])
print("Time to meet Margaret:", result[z])