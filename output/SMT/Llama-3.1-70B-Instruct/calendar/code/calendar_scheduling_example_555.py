from z3 import *

# Define the variables
StartTime = Int('StartTime')
EndTime = Int('EndTime')

# Define the constraints
s = Solver()

# Existing schedule of Randy
s.add(StartTime!= 9*60)
s.add(StartTime!= 11*60)
s.add(StartTime!= 16*60)

# Meeting duration
s.add(EndTime - StartTime == 30)

# Work hours
s.add(StartTime >= 9*60)
s.add(StartTime < 17*60)

# Evelyn's preference
s.add(StartTime < 13*60)

# Solve the constraints
if s.check() == sat:
    m = s.model()
    print("Day to meet: Monday")
    print("Start time:", m[StartTime].as_long()/60, ":", m[StartTime].as_long()%60)
    print("End time:", m[EndTime].as_long()/60, ":", m[EndTime].as_long()%60)
else:
    print("No solution found")