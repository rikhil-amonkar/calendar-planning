from z3 import *

# Define the variables
start_time_deborah = 1415  # 2:15 PM
end_time_deborah = 2000  # 8:00 PM
min_meeting_time = 75  # 1.25 hours
travel_time_castro_to_sun = 17  # 17 minutes
travel_time_sun_to_castro = 17  # 17 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave The Castro to meet Deborah
y = Int('y')  # Time to leave Sunset District to return to The Castro
z = Int('z')  # Time to meet Deborah

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at The Castro at 9:00 AM
s.add(x + travel_time_castro_to_sun >= start_time_deborah)  # Travel to Sunset District
s.add(x + travel_time_castro_to_sun + min_meeting_time <= end_time_deborah)  # Meet Deborah for at least 1.25 hours
s.add(z >= start_time_deborah)  # Meet Deborah
s.add(z <= end_time_deborah)  # Meet Deborah
s.add(y >= z)  # Leave Sunset District after meeting Deborah
s.add(y + travel_time_sun_to_castro <= 22 * 60)  # Return to The Castro by 10:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave The Castro to meet Deborah:", result[x])
print("Time to leave Sunset District to return to The Castro:", result[y])
print("Time to meet Deborah:", result[z])