from z3 import *

# Define the variables
start_time_laura = 0  # 8:00 AM
end_time_laura = 660  # 11:00 AM
min_meeting_time = 15  # 15 minutes
travel_time_castro_to_embarcadero = 22  # 22 minutes
travel_time_embarcadero_to_castro = 25  # 25 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave The Castro to meet Laura
y = Int('y')  # Time to leave Embarcadero to return to The Castro
z = Int('z')  # Time to meet Laura

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at The Castro at 9:00 AM
s.add(x + travel_time_castro_to_embarcadero >= start_time_laura)  # Travel to Embarcadero
s.add(x + travel_time_castro_to_embarcadero + min_meeting_time <= end_time_laura)  # Meet Laura for at least 15 minutes
s.add(z >= start_time_laura)  # Meet Laura
s.add(z <= end_time_laura)  # Meet Laura
s.add(y >= z)  # Leave Embarcadero after meeting Laura
s.add(y + travel_time_embarcadero_to_castro <= 11 * 60)  # Return to The Castro by 11:00 AM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave The Castro to meet Laura:", result[x])
print("Time to leave Embarcadero to return to The Castro:", result[y])
print("Time to meet Laura:", result[z])