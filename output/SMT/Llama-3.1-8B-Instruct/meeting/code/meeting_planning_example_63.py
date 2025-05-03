from z3 import *

# Define the variables
start_time_nancy = 0  # 7:15 AM
end_time_nancy = 1530  # 5:30 PM
min_meeting_time = 30  # 30 minutes
travel_time_presidio_to_bayview = 31  # 31 minutes
travel_time_bayview_to_presidio = 31  # 31 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Presidio to meet Nancy
y = Int('y')  # Time to leave Bayview to return to Presidio
z = Int('z')  # Time to meet Nancy

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Presidio at 9:00 AM
s.add(x + travel_time_presidio_to_bayview >= start_time_nancy)  # Travel to Bayview
s.add(x + travel_time_presidio_to_bayview + min_meeting_time <= end_time_nancy)  # Meet Nancy for at least 30 minutes
s.add(z >= start_time_nancy)  # Meet Nancy
s.add(z <= end_time_nancy)  # Meet Nancy
s.add(y >= z)  # Leave Bayview after meeting Nancy
s.add(y + travel_time_bayview_to_presidio <= 20 * 60)  # Return to Presidio by 6:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Presidio to meet Nancy:", result[x])
print("Time to leave Bayview to return to Presidio:", result[y])
print("Time to meet Nancy:", result[z])