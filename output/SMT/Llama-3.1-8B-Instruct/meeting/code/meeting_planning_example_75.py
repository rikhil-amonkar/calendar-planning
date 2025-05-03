from z3 import *

# Define the variables
start_time_david = 1130  # 11:30 AM
end_time_david = 1345  # 2:45 PM
min_meeting_time = 15  # 15 minutes
travel_time_pacific_to_fisherman = 13  # 13 minutes
travel_time_fisherman_to_pacific = 12  # 12 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Pacific Heights to meet David
y = Int('y')  # Time to leave Fisherman's Wharf to return to Pacific Heights
z = Int('z')  # Time to meet David

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Pacific Heights at 9:00 AM
s.add(x + travel_time_pacific_to_fisherman >= start_time_david)  # Travel to Fisherman's Wharf
s.add(x + travel_time_pacific_to_fisherman + min_meeting_time <= end_time_david)  # Meet David for at least 15 minutes
s.add(z >= start_time_david)  # Meet David
s.add(z <= end_time_david)  # Meet David
s.add(y >= z)  # Leave Fisherman's Wharf after meeting David
s.add(y + travel_time_fisherman_to_pacific <= 16 * 60)  # Return to Pacific Heights by 4:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Pacific Heights to meet David:", result[x])
print("Time to leave Fisherman's Wharf to return to Pacific Heights:", result[y])
print("Time to meet David:", result[z])