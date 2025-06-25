from z3 import *

# Define the variables
kenneth_meeting = Int('kenneth_meeting')
barbara_meeting = Int('barbara_meeting')

# Define the constraints
s = Optimize()
s.add(kenneth_meeting >= 90)  # Minimum meeting time with Kenneth
s.add(kenneth_meeting <= 3)  # Maximum meeting time with Kenneth (3 hours)
s.add(barbara_meeting >= 45)  # Minimum meeting time with Barbara
s.add(barbara_meeting <= 11)  # Maximum meeting time with Barbara (11 hours)

# Objective function: maximize the total meeting time
s.maximize(kenneth_meeting + barbara_meeting)

# Kenneth is available from 12:00PM to 3:00PM
s.add(kenneth_meeting >= 12)  # Kenneth meeting time must be after arrival
s.add(kenneth_meeting <= 15)  # Kenneth meeting time must be before departure

# Barbara is available from 8:15AM to 7:00PM
s.add(barbara_meeting >= 8)  # Barbara meeting time must be after arrival
s.add(barbara_meeting <= 19)  # Barbara meeting time must be before departure

# Solve the optimization problem
solution = s.check()
if solution == sat:
    model = s.model()
    print("SOLUTION:")
    print(f"Kenneth meeting time: {model[kenneth_meeting].as_long()} hours")
    print(f"Barbara meeting time: {model[barbara_meeting].as_long()} hours")
else:
    print("No solution found.")