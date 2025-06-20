from z3 import *

# Define the variables
sunset_arrival = 0  # Time you arrive at Sunset District
sunset_leave = 0    # Time you leave Sunset District
park_arrival = 0    # Time you arrive at Golden Gate Park
park_leave = 0      # Time you leave Golden Gate Park
park_time = 0       # Time you spend at Golden Gate Park
visit_joshua = Bool('visit_joshua')  # Whether you visit Joshua or not
visit_joshua_time = If(visit_joshua, park_time, 0)  # Time you spend with Joshua if you visit him

# Define the constraints
s = Solver()

# You arrive at Sunset District at 9:00AM
s.add(sunset_arrival == 540)  # 540 minutes after midnight (9:00AM)

# You must meet with exactly one person
s.add(Not(Or(visit_joshua, park_arrival!= park_leave)))  # You visit Joshua or you don't visit Joshua and arrive and leave Golden Gate Park at the same time

# Travel times
s.add(sunset_leave == sunset_arrival + 11)  # Travel from Sunset District to Golden Gate Park
s.add(park_arrival == sunset_leave + 10)  # Travel from Golden Gate Park to Sunset District
s.add(park_leave == park_arrival + visit_joshua_time)  # You leave Golden Gate Park after spending time with Joshua

# Solve the constraints
s.add(park_time >= 15)  # You spend at least 15 minutes with Joshua
s.add(park_arrival >= 513)  # You arrive at Golden Gate Park after 8:45PM
s.add(park_leave <= 549)  # You leave Golden Gate Park before 9:45PM
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