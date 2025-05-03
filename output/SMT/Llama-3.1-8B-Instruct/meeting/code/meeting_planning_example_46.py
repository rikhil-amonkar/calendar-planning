from z3 import *

# Define the variables
start_time_robert = 1730  # 4:30 PM
end_time_robert = 2130  # 9:30 PM
min_meeting_time = 90  # 1.5 hours
travel_time_haight_to_north = 19  # 19 minutes
travel_time_north_to_haight = 18  # 18 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Haight-Ashbury to meet Robert
y = Int('y')  # Time to leave North Beach to return to Haight-Ashbury
z = Int('z')  # Time to meet Robert

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Haight-Ashbury at 9:00 AM
s.add(x + travel_time_haight_to_north >= start_time_robert)  # Travel to North Beach
s.add(x + travel_time_haight_to_north + min_meeting_time <= end_time_robert)  # Meet Robert for at least 1.5 hours
s.add(z >= start_time_robert)  # Meet Robert
s.add(z <= end_time_robert)  # Meet Robert
s.add(y >= z)  # Leave North Beach after meeting Robert
s.add(y + travel_time_north_to_haight <= 24 * 60)  # Return to Haight-Ashbury by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Haight-Ashbury to meet Robert:", result[x])
print("Time to leave North Beach to return to Haight-Ashbury:", result[y])
print("Time to meet Robert:", result[z])