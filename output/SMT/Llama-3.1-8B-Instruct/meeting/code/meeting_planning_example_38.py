from z3 import *

# Define the variables
start_time_margaret = 2345  # 9:45 PM
end_time_margaret = 2350  # 10:30 PM
min_meeting_time = 45  # 45 minutes
travel_time_union_to_north = 10  # 10 minutes
travel_time_north_to_union = 7  # 7 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Union Square to meet Margaret
y = Int('y')  # Time to leave North Beach to return to Union Square
z = Int('z')  # Time to meet Margaret

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Union Square at 9:00 AM
s.add(x + travel_time_union_to_north >= start_time_margaret)  # Travel to North Beach
s.add(x + travel_time_union_to_north + min_meeting_time <= end_time_margaret)  # Meet Margaret for at least 45 minutes
s.add(z >= start_time_margaret)  # Meet Margaret
s.add(z <= end_time_margaret)  # Meet Margaret
s.add(y >= z)  # Leave North Beach after meeting Margaret
s.add(y + travel_time_north_to_union <= 24 * 60)  # Return to Union Square by 12:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Union Square to meet Margaret:", result[x])
print("Time to leave North Beach to return to Union Square:", result[y])
print("Time to meet Margaret:", result[z])