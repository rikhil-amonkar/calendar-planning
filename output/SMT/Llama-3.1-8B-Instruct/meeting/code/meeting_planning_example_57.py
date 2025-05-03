from z3 import *

# Define the variables
start_time_jessica = 630  # 10:30 AM
end_time_jessica = 1745  # 5:45 PM
min_meeting_time = 60  # 1 hour
travel_time_bayview_to_sun = 23  # 23 minutes
travel_time_sun_to_bayview = 22  # 22 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Bayview to meet Jessica
y = Int('y')  # Time to leave Sunset District to return to Bayview
z = Int('z')  # Time to meet Jessica

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Bayview at 9:00 AM
s.add(x + travel_time_bayview_to_sun >= start_time_jessica)  # Travel to Sunset District
s.add(x + travel_time_bayview_to_sun + min_meeting_time <= end_time_jessica)  # Meet Jessica for at least 1 hour
s.add(z >= start_time_jessica)  # Meet Jessica
s.add(z <= end_time_jessica)  # Meet Jessica
s.add(y >= z)  # Leave Sunset District after meeting Jessica
s.add(y + travel_time_sun_to_bayview <= 20 * 60)  # Return to Bayview by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Bayview to meet Jessica:", result[x])
print("Time to leave Sunset District to return to Bayview:", result[y])
print("Time to meet Jessica:", result[z])