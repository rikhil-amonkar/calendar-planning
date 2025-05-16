from z3 import *

# Define the variables
Day = Int('Day')
StartTime = Int('StartTime')
EndTime = Int('EndTime')

# Define the constraints
s = Solver()

# Existing schedule of Martha
s.add(Or(Day!= 1, StartTime!= 16*60))
s.add(Or(Day!= 2, StartTime!= 15*60))
s.add(Or(Day!= 3, StartTime!= 10*60))
s.add(Or(Day!= 3, StartTime!= 14*60))

# Existing schedule of Beverly
s.add(Or(Day!= 1, StartTime!= 9*60))
s.add(Or(Day!= 1, StartTime!= 14*60))
s.add(Or(Day!= 2, StartTime!= 9*60))
s.add(Or(Day!= 3, StartTime!= 9*60 + 30))
s.add(Or(Day!= 3, StartTime!= 16*60 + 30))

# Meeting duration
s.add(EndTime - StartTime == 60)

# Work hours
s.add(StartTime >= 9*60)
s.add(StartTime < 17*60)

# Day constraints
s.add(Day >= 1)  # Monday
s.add(Day <= 3)  # Wednesday

# Solve the constraints
if s.check() == sat:
    m = s.model()
    days = ['Monday', 'Tuesday', 'Wednesday']
    print("Day to meet:", days[m[Day].as_long() - 1])
    print("Start time:", m[StartTime].as_long()/60, ":", m[StartTime].as_long()%60)
    print("End time:", m[EndTime].as_long()/60, ":", m[EndTime].as_long()%60)
else:
    print("No solution found")