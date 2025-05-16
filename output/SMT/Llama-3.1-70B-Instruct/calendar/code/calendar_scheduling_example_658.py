from z3 import *

# Define the variables
Day = Int('Day')
StartTime = Int('StartTime')
EndTime = Int('EndTime')

# Define the constraints
s = Solver()

# Existing schedule of Shirley
ShirleyConstraints = [StartTime!= 10*60 + 30, StartTime!= 12*60, StartTime!= 16*60, 
                      StartTime!= 9*60 + 30]

# Existing schedule of Albert
AlbertConstraints = [StartTime!= 9*60, StartTime!= 9*60 + 30, StartTime!= 11*60, 
                    StartTime!= 11*60 + 30, StartTime!= 13*60, StartTime!= 16*60 + 30]

# Meeting duration
s.add(EndTime - StartTime == 30)

# Work hours
s.add(StartTime >= 9*60)
s.add(StartTime < 17*60)

# Day constraints
s.add(Day >= 1)  # Monday
s.add(Day <= 2)  # Tuesday

# Shirley's preference
s.add(Or(Day!= 2, StartTime < 10*60 + 30))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    print("Day to meet:", m[Day].as_long())
    print("Start time:", m[StartTime].as_long()/60, ":", m[StartTime].as_long()%60)
    print("End time:", m[EndTime].as_long()/60, ":", m[EndTime].as_long()%60)
else:
    print("No solution found")