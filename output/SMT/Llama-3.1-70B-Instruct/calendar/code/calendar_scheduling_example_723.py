from z3 import *

# Define the variables
Arthur = Int('Arthur')
Michael = Int('Michael')
Day = Int('Day')
StartTime = Int('StartTime')
EndTime = Int('EndTime')

# Define the constraints
s = Solver()

# Existing schedule of Arthur
ArthurConstraints = [Arthur!= 11*60, Arthur!= 13*60 + 30, Arthur!= 15*60, 
                     Arthur!= 13*60, Arthur!= 16*60, 
                     Arthur!= 10*60, Arthur!= 11*60, Arthur!= 12*60, 
                     Arthur!= 14*60, Arthur!= 16*60]

# Existing schedule of Michael
MichaelConstraints = [Michael!= 9*60, Michael!= 12*60 + 30, Michael!= 14*60, 
                      Michael!= 15*60, 
                      Michael!= 9*60 + 30, Michael!= 12*60, 
                      Michael!= 14*60, 
                      Michael!= 10*60, Michael!= 13*60]

# Meeting duration
s.add(EndTime - StartTime == 30)

# Work hours
s.add(StartTime >= 9*60)
s.add(StartTime < 17*60)

# Day constraints
s.add(Day >= 1)  # Monday
s.add(Day <= 3)  # Wednesday

# Arthur's availability
ArthurAvailable = [10*60, 12*60, 13*60 + 30, 15*60 + 30, 16*60 + 30, 
                   9*60, 11*60 + 30, 12*60 + 30, 13*60 + 60, 14*60 + 30, 
                   9*60, 12*60 + 30, 13*60 + 60, 14*60 + 60]
s.add(Or([StartTime == a for a in ArthurAvailable]))

# Michael's availability
MichaelAvailable = [12*60, 13*60, 14*60 + 30, 
                    11*60 + 30, 13*60 + 30, 15*60 + 30, 
                    12*60 + 30, 13*60 + 60]
s.add(Or([StartTime == m for m in MichaelAvailable]))

# Arthur can not meet on Tuesday
s.add(Day!= 2)

# Find the earliest time
s.add(StartTime < 1000)  # Large number

# Solve the constraints
if s.check() == sat:
    m = s.model()
    print("Day to meet:", m[Day].as_long())
    print("Start time:", m[StartTime].as_long()/60, ":", m[StartTime].as_long()%60)
    print("End time:", m[EndTime].as_long()/60, ":", m[EndTime].as_long()%60)
else:
    print("No solution found")