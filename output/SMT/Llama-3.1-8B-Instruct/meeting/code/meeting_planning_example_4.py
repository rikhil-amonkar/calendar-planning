from z3 import *

# Define the variables
start_time_jessica = 915  # 9:15 AM
end_time_jessica = 1745  # 5:45 PM
min_meeting_time = 60  # 1 hour
travel_time_presidio_to_marina = 10  # 10 minutes
travel_time_marina_to_presidio = 10  # 10 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Presidio to meet Jessica
y = Int('y')  # Time to leave Marina District to return to Presidio
z = Int('z')  # Time to meet Jessica

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Presidio at 9:00 AM
s.add(x + travel_time_presidio_to_marina >= start_time_jessica)  # Travel to Marina District
s.add(x + travel_time_presidio_to_marina + min_meeting_time <= end_time_jessica)  # Meet Jessica for at least 1 hour
s.add(z >= start_time_jessica)  # Meet Jessica
s.add(z <= end_time_jessica)  # Meet Jessica
s.add(y >= z)  # Leave Marina District after meeting Jessica
s.add(y + travel_time_marina_to_presidio <= 18 * 60)  # Return to Presidio by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Presidio to meet Jessica:", result[x])
print("Time to leave Marina District to return to Presidio:", result[y])
print("Time to meet Jessica:", result[z])