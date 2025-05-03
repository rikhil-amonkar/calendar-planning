from z3 import *

# Define the variables
start_time_jessica = 315  # 3:15 PM
end_time_jessica = 1815  # 6:15 PM
min_meeting_time = 90  # 1.5 hours
travel_time_haight_to_sunet = 15  # 15 minutes
travel_time_sunet_to_haight = 15  # 15 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Haight-Ashbury to meet Jessica
y = Int('y')  # Time to leave Sunset District to return to Haight-Ashbury
z = Int('z')  # Time to meet Jessica

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Haight-Ashbury at 9:00 AM
s.add(x + travel_time_haight_to_sunet >= start_time_jessica)  # Travel to Sunset District
s.add(x + travel_time_haight_to_sunet + min_meeting_time <= end_time_jessica)  # Meet Jessica for at least 1.5 hours
s.add(z >= start_time_jessica)  # Meet Jessica
s.add(z <= end_time_jessica)  # Meet Jessica
s.add(y >= z)  # Leave Sunset District after meeting Jessica
s.add(y + travel_time_sunet_to_haight <= 20 * 60)  # Return to Haight-Ashbury by 8:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Haight-Ashbury to meet Jessica:", result[x])
print("Time to leave Sunset District to return to Haight-Ashbury:", result[y])
print("Time to meet Jessica:", result[z])