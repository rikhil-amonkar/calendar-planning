from z3 import *

# Define the variables
sunset_arrival = 0  # Time you arrive at Sunset District
sunset_leave = 0    # Time you leave Sunset District
park_arrival = 0    # Time you arrive at Golden Gate Park
park_leave = 0      # Time you leave Golden Gate Park
park_time = 0       # Time you spend at Golden Gate Park
visit_joshua = Bool('visit_joshua')  # Whether you visit Joshua or not

# Define the constraints
s = Solver()

# You arrive at Sunset District at 9:00AM
s.add(sunset_arrival == 540)  # 540 minutes after midnight (9:00AM)

# You must meet with exactly one person
s.add(Or(Not(visit_joshua), park_arrival == park_leave))  # You visit Joshua or you don't visit Joshua and arrive and leave Golden Gate Park at the same time
s.add(And(visit_joshua, park_arrival >= 513))  # You visit Joshua and arrive at Golden Gate Park after 8:45PM
s.add(And(visit_joshua, park_leave <= 549))  # You visit Joshua and leave Golden Gate Park before 9:45PM
s.add(And(visit_joshua, park_time >= 15))  # You visit Joshua and spend at least 15 minutes with him
s.add(Not(visit_joshua) == (park_arrival == 0))  # If you don't visit Joshua, you don't arrive at Golden Gate Park

# Travel times
s.add(sunset_leave == sunset_arrival + 11)  # Travel from Sunset District to Golden Gate Park
s.add(Or(And(visit_joshua, park_arrival == sunset_leave + 10), Not(visit_joshua)))  # Travel from Golden Gate Park to Sunset District if you visit Joshua or not

# Solve the constraints
s.check()

# Print the solution
if s.check() == sat:
    m = s.model()
    if m[visit_joshua].as_bool():
        print("Optimal schedule:")
        print(f"Arrive at Sunset District: {m[sunset_arrival].as_long()} minutes after midnight")
        print(f"Leave Sunset District: {m[sunset_leave].as_long()} minutes after midnight")
        print(f"Arrive at Golden Gate Park: {m[park_arrival].as_long()} minutes after midnight")
        print(f"Leave Golden Gate Park: {m[park_leave].as_long()} minutes after midnight")
        print(f"Time spent at Golden Gate Park: {m[park_time].as_long()} minutes")
    else:
        print("You don't visit Joshua.")
else:
    print("No solution found")