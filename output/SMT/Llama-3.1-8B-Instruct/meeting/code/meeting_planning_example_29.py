from z3 import *

# Define the variables
start_time_nancy = 1830  # 7:30 PM
end_time_nancy = 2145  # 9:45 PM
min_meeting_time = 75  # 1.25 hours
travel_time_sunset_to_haight = 15  # 15 minutes
travel_time_haight_to_sunset = 15  # 15 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Sunset District to meet Nancy
y = Int('y')  # Time to leave Haight-Ashbury to return to Sunset District
z = Int('z')  # Time to meet Nancy

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Sunset District at 9:00 AM
s.add(x + travel_time_sunset_to_haight >= start_time_nancy)  # Travel to Haight-Ashbury
s.add(x + travel_time_sunset_to_haight + min_meeting_time <= end_time_nancy)  # Meet Nancy for at least 1.25 hours
s.add(z >= start_time_nancy)  # Meet Nancy
s.add(z <= end_time_nancy)  # Meet Nancy
s.add(y >= z)  # Leave Haight-Ashbury after meeting Nancy
s.add(y + travel_time_haight_to_sunset <= 24 * 60)  # Return to Sunset District by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Sunset District to meet Nancy:", result[x])
print("Time to leave Haight-Ashbury to return to Sunset District:", result[y])
print("Time to meet Nancy:", result[z])