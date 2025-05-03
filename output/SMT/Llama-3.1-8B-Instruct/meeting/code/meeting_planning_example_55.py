from z3 import *

# Define the variables
start_time_helen = 1230  # 11:30 AM
end_time_helen = 1215  # 12:15 PM
min_meeting_time = 45  # 45 minutes
travel_time_financial_to_nob = 8  # 8 minutes
travel_time_nob_to_financial = 9  # 9 minutes

# Define the solver
s = Optimize()

# Define the variables
x = Int('x')  # Time to leave Financial District to meet Helen
y = Int('y')  # Time to leave Nob Hill to return to Financial District
z = Int('z')  # Time to meet Helen

# Define the constraints
s.add(x >= 9 * 60)  # You arrive at Financial District at 9:00 AM
s.add(x + travel_time_financial_to_nob >= start_time_helen)  # Travel to Nob Hill
s.add(x + travel_time_financial_to_nob + min_meeting_time <= end_time_helen)  # Meet Helen for at least 45 minutes
s.add(z >= start_time_helen)  # Meet Helen
s.add(z <= end_time_helen)  # Meet Helen
s.add(y >= z)  # Leave Nob Hill after meeting Helen
s.add(y + travel_time_nob_to_financial <= 12 * 60)  # Return to Financial District by 12:00 PM

# Define the objective function
s.add(x + y)  # Minimize the total time spent

# Solve the optimization problem
s.check()
result = s.value()

# Print the result
print("Time to leave Financial District to meet Helen:", result[x])
print("Time to leave Nob Hill to return to Financial District:", result[y])
print("Time to meet Helen:", result[z])