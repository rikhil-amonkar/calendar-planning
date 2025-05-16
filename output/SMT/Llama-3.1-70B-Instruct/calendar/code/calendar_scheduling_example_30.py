from z3 import *

# Define the variables
StartTime = Int('StartTime')
EndTime = Int('EndTime')

# Define the constraints
s = Solver()

# Existing schedule of Jeffrey
s.add(StartTime!= 9*60 + 30)
s.add(StartTime!= 10*60 + 30)

# Existing schedule of Virginia
s.add(StartTime!= 9*60)
s.add(StartTime!= 10*60)
s.add(StartTime!= 14*60 + 30)
s.add(StartTime!= 16*60)

# Existing schedule of Melissa
s.add(StartTime!= 9*60)
s.add(StartTime!= 10*60)
s.add(StartTime!= 11*60)
s.add(StartTime!= 12*60)
s.add(StartTime!= 13*60)
s.add(StartTime!= 16*60)

# Meeting duration
s.add(EndTime - StartTime == 30)

# Work hours
s.add(StartTime >= 9*60)
s.add(StartTime < 17*60)

# Melissa's preference
s.add(Or(StartTime < 14*60, StartTime == 0))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    print("Day to meet: Monday")
    print("Start time:", m[StartTime].as_long()/60, ":", m[StartTime].as_long()%60)
    print("End time:", m[EndTime].as_long()/60, ":", m[EndTime].as_long()%60)
else:
    print("No solution found")