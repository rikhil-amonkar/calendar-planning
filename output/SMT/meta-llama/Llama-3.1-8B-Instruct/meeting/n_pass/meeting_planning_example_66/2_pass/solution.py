from z3 import *

# Define the variables
nob_hill_start = Int('nob_hill_start')
presidio_start = Int('presidio_start')
nob_hill_end = Int('nob_hill_end')
presidio_end = Int('presidio_end')
friend_start = Int('friend_start')
friend_end = Int('friend_end')

# Define the constraints
s = Optimize()

# We arrive at Nob Hill at 9:00AM
s.add(nob_hill_start == 9 * 60)

# We want to meet Robert for at least 120 minutes
s.add(presidio_end - presidio_start >= 120)

# Travel time from Nob Hill to Presidio
s.add(presidio_start >= nob_hill_end + 17)

# Travel time from Presidio to Nob Hill
s.add(nob_hill_end >= presidio_end + 18)

# Robert is at Presidio from 11:15AM to 5:45PM
s.add(presidio_start >= 11 * 60 + 15)
s.add(presidio_end <= 17 * 60 + 45)

# Ensure that we don't spend more than 24 hours at each location
s.add(nob_hill_end - nob_hill_start <= 24 * 60)
s.add(presidio_end - presidio_start <= 24 * 60)

# Friend is at Presidio from 11:15AM to 5:45PM
s.add(friend_start >= 11 * 60 + 15)
s.add(friend_end <= 17 * 60 + 45)

# We can't visit the friend at the same time as Robert
s.add(Or(presidio_start + 120 > friend_start, presidio_end < friend_start))
s.add(Or(friend_start + 120 > presidio_start, friend_end < presidio_start))

# Objective: minimize the total time spent at all locations
s.minimize((nob_hill_end - nob_hill_start) + (presidio_end - presidio_start) + (friend_end - friend_start))

# Solve the optimization problem
if s.check() == sat:
    model = s.model()
    print("Nob Hill start time:", model[nob_hill_start].as_long())
    print("Presidio start time:", model[presidio_start].as_long())
    print("Nob Hill end time:", model[nob_hill_end].as_long())
    print("Presidio end time:", model[presidio_end].as_long())
    print("Friend start time:", model[friend_start].as_long())
    print("Friend end time:", model[friend_end].as_long())
else:
    print("No solution found")