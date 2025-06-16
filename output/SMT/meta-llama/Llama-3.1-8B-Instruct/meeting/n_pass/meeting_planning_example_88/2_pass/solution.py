from z3 import *

# Define the variables
sunset_arrival = 0  # Time you arrive at Sunset District
sunset_leave = 0    # Time you leave Sunset District
park_arrival = 0    # Time you arrive at Golden Gate Park
park_leave = 0      # Time you leave Golden Gate Park
park_time = 0       # Time you spend at Golden Gate Park

# Define the constraints
s = Solver()

# You arrive at Sunset District at 9:00AM
s.add(sunset_arrival == 540)  # 540 minutes after midnight (9:00AM)

# You spend at least 15 minutes with Joshua
s.add(park_time >= 15)

# You can't arrive at Golden Gate Park before Joshua starts
s.add(park_arrival >= 513)  # 513 minutes after midnight (8:45PM)

# You can't leave Golden Gate Park after Joshua finishes
s.add(park_leave <= 549)    # 549 minutes after midnight (9:45PM)

# You must meet with exactly one person
s.add(park_arrival == park_leave)  # You arrive and leave Golden Gate Park at the same time
s.add(park_time == park_arrival - (sunset_arrival + 11))  # You spend the time you arrive at Golden Gate Park minus travel time from Sunset District

# Solve the constraints
s.check()

# Print the solution
if s.check() == sat:
    m = s.model()
    print("Optimal schedule:")
    print(f"Arrive at Sunset District: {m[sunset_arrival].as_long()} minutes after midnight")
    print(f"Leave Sunset District: {m[sunset_leave].as_long()} minutes after midnight")
    print(f"Arrive at Golden Gate Park: {m[park_arrival].as_long()} minutes after midnight")
    print(f"Leave Golden Gate Park: {m[park_leave].as_long()} minutes after midnight")
    print(f"Time spent at Golden Gate Park: {m[park_time].as_long()} minutes")
else:
    print("No solution found")