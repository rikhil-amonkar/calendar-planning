from z3 import *

# Define variables for start times and activity indices
start1 = Int('start1')
start2 = Int('start2')
start3 = Int('start3')
idx1 = Int('idx1')
idx2 = Int('idx2')
idx3 = Int('idx3')

# Create solver instance
s = Solver()

# Activity index constraints (must be 0, 1, or 2)
s.add(Or(idx1 == 0, idx1 == 1, idx1 == 2))
s.add(Or(idx2 == 0, idx2 == 1, idx2 == 2))
s.add(Or(idx3 == 0, idx3 == 1, idx3 == 2))

# Activity index uniqueness
s.add(Distinct(idx1, idx2, idx3))

# Duration constraints (each activity lasts 3 hours)
s.add(start1 >= 0, start1 <= 21)  # 21 ensures end time <= 24
s.add(start2 >= 0, start2 <= 21)
s.add(start3 >= 0, start3 <= 21)

# Time slot constraints based on activity indices
s.add(If(idx1 == 0, And(start1 >= 8, start1 <= 10), True))
s.add(If(idx1 == 1, And(start1 >= 11, start1 <= 15), True))
s.add(If(idx1 == 2, And(start1 >= 16, start1 <= 20), True))

s.add(If(idx2 == 0, And(start2 >= 8, start2 <= 10), True))
s.add(If(idx2 == 1, And(start2 >= 11, start2 <= 15), True))
s.add(If(idx2 == 2, And(start2 >= 16, start2 <= 20), True))

s.add(If(idx3 == 0, And(start3 >= 8, start3 <= 10), True))
s.add(If(idx3 == 1, And(start3 >= 11, start3 <= 15), True))
s.add(If(idx3 == 2, And(start3 >= 16, start3 <= 20), True))

# Temporal separation: Activities cannot overlap
s.add(Or(
    start1 + 3 <= start2,
    start2 + 3 <= start1
))
s.add(Or(
    start1 + 3 <= start3,
    start3 + 3 <= start1
))
s.add(Or(
    start2 + 3 <= start3,
    start3 + 3 <= start2
))

# Solve and print the schedule
if s.check() == sat:
    m = s.model()
    print("Activity 1: index={}, start={}".format(m[idx1], m[start1]))
    print("Activity 2: index={}, start={}".format(m[idx2], m[start2]))
    print("Activity 3: index={}, start={}".format(m[idx3], m[start3]))
else:
    print("No valid schedule found")