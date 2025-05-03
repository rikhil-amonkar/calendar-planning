from z3 import *

# We have a 13-day trip visiting 3 European cities.
# The requirements are:
#   • Nice: 7 days and you will attend a wedding in Nice between day 1 and day 7.
#   • Copenhagen: 2 days.
#   • Tallinn: 6 days.
#
# The available direct flights are:
#   • between Nice and Copenhagen,
#   • between Copenhagen and Tallinn.
#
# We assume the following itinerary order:
#   Nice -> Copenhagen -> Tallinn.
#
# Using the convention that when you take a direct flight on a day,
# that day counts as both the last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Nice to Copenhagen.
#   d2 = flight day from Copenhagen to Tallinn.
#
# Then the segments (with overlapping flight days) are defined as:
#
# 1. Nice segment:
#    From Day 1 to Day d1, duration = d1 days.
#    We require 7 days in Nice, so: d1 = 7.
#
# 2. Copenhagen segment:
#    From Day d1 to Day d2, duration = (d2 - d1 + 1) days.
#    We require 2 days in Copenhagen, so: d2 - d1 + 1 = 2, which gives d2 = d1 + 1.
#    With d1 = 7, we get d2 = 8.
#
# 3. Tallinn segment:
#    From Day d2 to Day 13, duration = (13 - d2 + 1) days.
#    We require 6 days in Tallinn, so: 13 - d2 + 1 = 6, which gives 14 - d2 = 6.
#    Solving for d2, we get d2 = 8.
#
# The wedding in Nice is held between Day 1 and Day 7, and since the Nice segment spans Days 1 through 7, the requirement is satisfied.
#
# Final Itinerary:
#   • Stay in Nice from Day 1 to Day 7 (7 days). 
#       -> Attend the wedding in Nice during this period.
#       -> On Day 7, take a direct flight from Nice to Copenhagen.
#   • Stay in Copenhagen from Day 7 to Day 8 (2 days).
#       -> On Day 8, take a direct flight from Copenhagen to Tallinn.
#   • Stay in Tallinn from Day 8 to Day 13 (6 days).

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Nice to Copenhagen.
d2 = Int('d2')  # Flight day from Copenhagen to Tallinn.

# Constraint for Nice: duration from Day 1 to d1 must be 7 days.
s.add(d1 == 7)

# Constraint for Copenhagen: duration from d1 to d2 must be 2 days.
s.add(d2 - d1 + 1 == 2)

# Constraint for Tallinn: duration from d2 to Day 13 must be 6 days.
s.add(13 - d2 + 1 == 6)

# Enforce proper flight ordering and valid day boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 13)

# The wedding in Nice should occur between day 1 and day 7.
# This is ensured by the Nice segment being from Day 1 to d1 (where d1 == 7).

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 7 (flight from Nice to Copenhagen)
    d2_val = m[d2].as_long()  # Expected: 8 (flight from Copenhagen to Tallinn)
    
    print("Trip plan found:\n")
    
    # Nice segment.
    print("1. Stay in Nice from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> Attend the wedding in Nice between Day 1 and Day 7.")
    print("   -> On Day {}, take a direct flight from Nice to Copenhagen.".format(d1_val))
    
    # Copenhagen segment.
    print("2. Stay in Copenhagen from Day {} to Day {} (2 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Copenhagen to Tallinn.".format(d2_val))
    
    # Tallinn segment.
    print("3. Stay in Tallinn from Day {} to Day 13 (6 days).".format(d2_val))
else:
    print("No solution exists!")