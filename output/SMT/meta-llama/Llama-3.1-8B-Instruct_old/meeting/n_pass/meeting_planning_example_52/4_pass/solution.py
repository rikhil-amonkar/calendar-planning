from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time of the day (in minutes)
barbara_meeting = Int('barbara_meeting')  # Time spent meeting Barbara (in minutes)
richmond_district = Int('richmond_district')  # Time spent at Richmond District (in minutes)
russian_hill = Int('russian_hill')  # Time spent at Russian Hill (in minutes)

# Define the constraints
s = Optimize()
s.add(0 <= start_time)  # Start time must be non-negative
s.add(start_time <= 480)  # Start time must be before 8:00 PM
s.add(0 <= barbara_meeting)  # Time spent meeting Barbara must be non-negative
s.add(barbara_meeting == 45)  # Meet Barbara for exactly 45 minutes
s.add(0 <= richmond_district)  # Time spent at Richmond District must be non-negative
s.add(richmond_district <= 480)  # Time spent at Richmond District must be before 8:00 PM
s.add(0 <= russian_hill)  # Time spent at Russian Hill must be non-negative
s.add(russian_hill <= 480)  # Time spent at Russian Hill must be before 8:00 PM
s.add(start_time + 14 <= 585)  # Arrive at Richmond District before Barbara starts
s.add(start_time + 13 >= 585)  # Arrive at Russian Hill after Barbara starts
s.add(start_time + barbara_meeting + 13 >= 585)  # Leave Russian Hill after Barbara finishes
s.add(start_time + barbara_meeting + 14 >= 585)  # Leave Richmond District after Barbara finishes
s.add(russian_hill == 480 - 13 - 14)  # Spend exactly 453 minutes at Russian Hill
s.add(richmond_district == 27)  # Spend exactly 27 minutes at Richmond District

# Define the objective function
s.minimize(russian_hill + richmond_district)

# Solve the optimization problem
solution = s.check()
if solution == sat:
    model = s.model()
    print(f"Best schedule: Start at {model[start_time].as_long()} minutes, meet Barbara for 45 minutes, spend {model[russian_hill].as_long()} minutes at Russian Hill, and spend {model[richmond_district].as_long()} minutes at Richmond District.")
else:
    print("No solution found.")