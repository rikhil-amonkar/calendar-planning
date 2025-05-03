from z3 import *

# We have a 14-day trip visiting 3 cities with the following requirements:
#   • Helsinki: 6 days, and from Day 1 to Day 6 there is an annual show in Helsinki.
#   • Nice: 6 days.
#   • Mykonos: 4 days.
#
# Without overlaps the total would be 6 + 6 + 4 = 16 days.
# By overlapping flight days (each flight day counts as the last day in the departing city 
# and the first day in the arriving city), we plan the trip in 14 days.
#
# The available direct flights:
#   • between Helsinki and Nice,
#   • between Nice and Mykonos.
#
# We choose the itinerary ordering:
#   Helsinki -> Nice -> Mykonos.
#
# Let:
#   d1 = flight day from Helsinki to Nice.
#   d2 = flight day from Nice to Mykonos.
#
# Then the segments are:
#
# 1. Helsinki segment:
#    - Runs from Day 1 to Day d1.
#    - Duration = d1 days.
#    - Must be 6 days and cover the annual show (Day 1 to Day 6); so we set: d1 = 6.
#
# 2. Nice segment:
#    - Runs from Day d1 to Day d2.
#    - Duration = d2 - d1 + 1 days.
#    - Must be 6 days: d2 - d1 + 1 = 6 → with d1 = 6, this gives d2 = 11.
#
# 3. Mykonos segment:
#    - Runs from Day d2 to Day 14.
#    - Duration = 14 - d2 + 1 days.
#    - Must be 4 days: 14 - d2 + 1 = 4 → 15 - d2 = 4 → d2 = 11.
#
# Now we model these constraints using the Z3 solver.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Helsinki to Nice.
d2 = Int('d2')  # Flight day from Nice to Mykonos.

# Constraint for Helsinki segment (6 days and attending the show from Day 1 to Day 6)
s.add(d1 == 6)

# Constraint for Nice segment (6 days)
s.add(d2 - d1 + 1 == 6)

# Constraint for Mykonos segment (4 days)
s.add(14 - d2 + 1 == 4)

# Enforce ordering and valid day ranges.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 14)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 6 (Helsinki -> Nice flight on Day 6)
    d2_val = m[d2].as_long()  # Expected to be 11 (Nice -> Mykonos flight on Day 11)
    
    print("Trip plan found:\n")
    
    # Helsinki segment.
    print("1. Stay in Helsinki from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> Attend the annual show in Helsinki from Day 1 to Day 6.")
    print("   -> On Day {}, take a direct flight from Helsinki to Nice.".format(d1_val))
    
    # Nice segment.
    print("2. Stay in Nice from Day {} to Day {} (6 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Nice to Mykonos.".format(d2_val))
    
    # Mykonos segment.
    print("3. Stay in Mykonos from Day {} to Day 14 (4 days).".format(d2_val))
else:
    print("No solution exists!")