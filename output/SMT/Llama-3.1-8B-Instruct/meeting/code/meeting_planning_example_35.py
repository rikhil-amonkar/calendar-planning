from z3 import *

# Define the variables
start_time_jason = 0  # 8:30 AM
end_time_jason = 1230  # 12:30 PM
min_meeting_time = 90  # 1.5 hours
travel_time_bayview_to_chinatown = 18  # 18 minutes
travel_time_chinatown_to_bayview = 22  # 22 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Bayview to meet Jason
y = Int('y')  # Time to leave Chinatown to return to Bayview
z = Int('z')  # Time to meet Jason

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Bayview at 9:00 AM
s.add(x + travel_time_bayview_to_chinatown >= start_time_jason)  # Travel to Chinatown
s.add(x + travel_time_bayview_to_chinatown + min_meeting_time <= end_time_jason)  # Meet Jason for at least 1.5 hours
s.add(z >= start_time_jason)  # Meet Jason
s.add(z <= end_time_jason)  # Meet Jason
s.add(y >= z)  # Leave Chinatown after meeting Jason
s.add(y + travel_time_chinatown_to_bayview <= 12 * 60)  # Return to Bayview by 12:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Bayview to meet Jason:", result[x])
print("Time to leave Chinatown to return to Bayview:", result[y])
print("Time to meet Jason:", result[z])