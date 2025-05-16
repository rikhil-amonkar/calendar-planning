from z3 import *

# Define the variables
StartTime = Int('StartTime')
EndTime = Int('EndTime')

# Define the constraints
s = Solver()

# Existing schedule of Adam
s.add(StartTime!= 9*60 + 30)
s.add(StartTime!= 12*60 + 30)
s.add(StartTime!= 14*60 + 30)
s.add(StartTime!= 16*60 + 30)

# Existing schedule of Roy
s.add(StartTime!= 10*60)
s.add(StartTime!= 11*60 + 30)
s.add(StartTime!= 13*60 + 30)
s.add(StartTime!= 16*60 + 30)

# Meeting duration
s.add(EndTime - StartTime == 30)

# Work hours
s.add(StartTime >= 9*60)
s.add(StartTime < 17*60)

# Find the earliest time
s.add(StartTime < 1000)  # Large number

# Solve the constraints
if s.check() == sat:
    m = s.model()
    print("Day to meet: Monday")
    print("Start time:", m[StartTime].as_long()/60, ":", m[StartTime].as_long()%60)
    print("End time:", m[EndTime].as_long()/60, ":", m[EndTime].as_long()%60)
else:
    print("No solution found")