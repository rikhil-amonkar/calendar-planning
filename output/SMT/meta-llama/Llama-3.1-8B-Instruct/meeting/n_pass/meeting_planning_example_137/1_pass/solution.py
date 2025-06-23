from z3 import *

# Define the variables
start_time = Int('start_time')
end_time = Int('end_time')
kenneth_meeting = Int('kenneth_meeting')
barbara_meeting = Int('barbara_meeting')

# Define the constraints
s = Optimize()
s.add(start_time >= 0)  # Start time cannot be negative
s.add(end_time >= 0)  # End time cannot be negative
s.add(kenneth_meeting >= 0)  # Kenneth meeting time cannot be negative
s.add(barbara_meeting >= 0)  # Barbara meeting time cannot be negative

# Constraints for Kenneth
s.add(kenneth_meeting >= 90)  # Minimum meeting time with Kenneth
s.add(kenneth_meeting <= 3)  # Maximum meeting time with Kenneth (3 hours)
s.add(kenneth_meeting >= 12)  # Kenneth is available from 12:00PM
s.add(kenneth_meeting <= 15)  # Kenneth is available until 3:00PM

# Constraints for Barbara
s.add(barbara_meeting >= 45)  # Minimum meeting time with Barbara
s.add(barbara_meeting <= 11)  # Maximum meeting time with Barbara (11 hours)
s.add(barbara_meeting >= 8)  # Barbara is available from 8:15AM
s.add(barbara_meeting <= 19)  # Barbara is available until 7:00PM

# Objective function: maximize the total meeting time
s.maximize(kenneth_meeting + barbara_meeting)

# Solve the optimization problem
solution = s.check()
if solution == sat:
    model = s.model()
    print("SOLUTION:")
    print(f"Start time: {model[start_time].as_long()} hours")
    print(f"End time: {model[end_time].as_long()} hours")
    print(f"Kenneth meeting time: {model[kenneth_meeting].as_long()} hours")
    print(f"Barbara meeting time: {model[barbara_meeting].as_long()} hours")
else:
    print("No solution found.")