from z3 import *

# Define the variables
start_time_james = 0  # 8:30 AM
end_time_james = 1800  # 3:00 PM
min_meeting_time = 75  # 1.25 hours
travel_time_embarcadero_to_pacific = 11  # 11 minutes
travel_time_pacific_to_embarcadero = 10  # 10 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Embarcadero to meet James
y = Int('y')  # Time to leave Pacific Heights to return to Embarcadero
z = Int('z')  # Time to meet James

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Embarcadero at 9:00 AM
s.add(x + travel_time_embarcadero_to_pacific >= start_time_james)  # Travel to Pacific Heights
s.add(x + travel_time_embarcadero_to_pacific + min_meeting_time <= end_time_james)  # Meet James for at least 1.25 hours
s.add(z >= start_time_james)  # Meet James
s.add(z <= end_time_james)  # Meet James
s.add(y >= z)  # Leave Pacific Heights after meeting James
s.add(y + travel_time_pacific_to_embarcadero <= 18 * 60)  # Return to Embarcadero by 4:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Embarcadero to meet James:", result[x])
print("Time to leave Pacific Heights to return to Embarcadero:", result[y])
print("Time to meet James:", result[z])