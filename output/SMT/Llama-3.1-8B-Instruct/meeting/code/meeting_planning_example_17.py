from z3 import *

# Define the variables
start_time_matthew = 1330  # 1:30 PM
end_time_matthew = 1430  # 2:30 PM
min_meeting_time = 15  # 15 minutes
travel_time_alamo_to_sun = 16  # 16 minutes
travel_time_sun_to_alamo = 17  # 17 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Alamo Square to meet Matthew
y = Int('y')  # Time to leave Sunset District to return to Alamo Square
z = Int('z')  # Time to meet Matthew

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Alamo Square at 9:00 AM
s.add(x + travel_time_alamo_to_sun >= start_time_matthew)  # Travel to Sunset District
s.add(x + travel_time_alamo_to_sun + min_meeting_time <= end_time_matthew)  # Meet Matthew for at least 15 minutes
s.add(z >= start_time_matthew)  # Meet Matthew
s.add(z <= end_time_matthew)  # Meet Matthew
s.add(y >= z)  # Leave Sunset District after meeting Matthew
s.add(y + travel_time_sun_to_alamo <= 14 * 60)  # Return to Alamo Square by 2:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Alamo Square to meet Matthew:", result[x])
print("Time to leave Sunset District to return to Alamo Square:", result[y])
print("Time to meet Matthew:", result[z])