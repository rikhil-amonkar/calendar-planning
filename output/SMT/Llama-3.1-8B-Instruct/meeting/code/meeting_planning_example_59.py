from z3 import *

# Define the variables
start_time_richard = 0  # 7:00 AM
end_time_richard = 1345  # 3:45 PM
min_meeting_time = 105  # 1.75 hours
travel_time_bayview_to_haight = 19  # 19 minutes
travel_time_haight_to_bayview = 18  # 18 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Bayview to meet Richard
y = Int('y')  # Time to leave Haight-Ashbury to return to Bayview
z = Int('z')  # Time to meet Richard

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Bayview at 9:00 AM
s.add(x + travel_time_bayview_to_haight >= start_time_richard)  # Travel to Haight-Ashbury
s.add(x + travel_time_bayview_to_haight + min_meeting_time <= end_time_richard)  # Meet Richard for at least 1.75 hours
s.add(z >= start_time_richard)  # Meet Richard
s.add(z <= end_time_richard)  # Meet Richard
s.add(y >= z)  # Leave Haight-Ashbury after meeting Richard
s.add(y + travel_time_haight_to_bayview <= 17 * 60)  # Return to Bayview by 3:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Bayview to meet Richard:", result[x])
print("Time to leave Haight-Ashbury to return to Bayview:", result[y])
print("Time to meet Richard:", result[z])