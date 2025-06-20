from z3 import *

# Define the variables
nob_hill_start = Int('nob_hill_start')
nob_hill_end = Int('nob_hill_end')
friend_start = Int('friend_start')
friend_end = Int('friend_end')
friend_location = IntSort()('friend_location')
friend_time = IntSort()('friend_time')

# Define the constraints
s = Optimize()

# We arrive at Nob Hill at 9:00AM
s.add(nob_hill_start == 9 * 60)

# We want to meet Robert for at least 120 minutes
# friend_location can be either 0 (Nob Hill) or 1 (Presidio)
s.add(friend_time >= 11 * 60 + 15)
s.add(friend_time <= 17 * 60 + 45)
s.add(friend_location >= 0)
s.add(friend_location <= 1)

# Travel time from Nob Hill to Presidio
s.add(friend_start >= nob_hill_end + 17)
s.add(Implies(friend_location == 1, friend_start >= nob_hill_end + 17))

# Travel time from Presidio to Nob Hill
s.add(nob_hill_end >= friend_end + 18)
s.add(Implies(friend_location == 0, nob_hill_end >= friend_end + 18))

# Ensure that we don't spend more than 24 hours at each location
s.add(nob_hill_end - nob_hill_start <= 24 * 60)

# We can't visit the friend at the same time as Robert
s.add(Implies(friend_location == 1, friend_start + 120 > nob_hill_start))
s.add(Implies(friend_location == 1, nob_hill_end < friend_start))
s.add(Implies(friend_location == 0, nob_hill_start + 120 > friend_start))
s.add(Implies(friend_location == 0, friend_end < nob_hill_start))

# Objective: minimize the total time spent at all locations
s.minimize((nob_hill_end - nob_hill_start) + (friend_end - friend_start))

# Solve the optimization problem
if s.check() == sat:
    model = s.model()
    nob_hill_start_val = model[nob_hill_start].as_long()
    nob_hill_end_val = model[nob_hill_end].as_long()
    friend_start_val = model[friend_start].as_long()
    friend_end_val = model[friend_end].as_long()
    friend_location_val = model[friend_location].as_long()
    
    if friend_location_val == 0:
        print("Meet Robert at Nob Hill from", nob_hill_start_val, "to", nob_hill_end_val)
    else:
        print("Meet Robert at Presidio from", friend_start_val, "to", friend_end_val)
else:
    print("No solution found")