from z3 import *

# Define the variables
start_time_john = 1315  # 3:15 PM
end_time_john = 1515  # 3:15 PM
min_meeting_time = 75  # 1.25 hours
travel_time_richmond_to_north = 17  # 17 minutes
travel_time_north_to_richmond = 18  # 18 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Richmond District to meet John
y = Int('y')  # Time to leave North Beach to return to Richmond District
z = Int('z')  # Time to meet John

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Richmond District at 9:00 AM
s.add(x + travel_time_richmond_to_north >= start_time_john)  # Travel to North Beach
s.add(x + travel_time_richmond_to_north + min_meeting_time <= end_time_john)  # Meet John for at least 1.25 hours
s.add(z >= start_time_john)  # Meet John
s.add(z <= end_time_john)  # Meet John
s.add(y >= z)  # Leave North Beach after meeting John
s.add(y + travel_time_north_to_richmond <= 16 * 60)  # Return to Richmond District by 4:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Richmond District to meet John:", result[x])
print("Time to leave North Beach to return to Richmond District:", result[y])
print("Time to meet John:", result[z])