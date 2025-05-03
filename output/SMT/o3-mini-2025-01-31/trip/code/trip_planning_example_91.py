from z3 import *

# We have a 10-day trip visiting 3 cities with the following requirements:
#   • Krakow: 3 days.
#   • Vienna: 2 days.
#   • Riga: 7 days, and from Day 4 to Day 10 there is an annual show in Riga.
#
# Without overlapping, the total would be 3 + 2 + 7 = 12 days.
# Using overlapping flight days (each flight day counts as both the last day in one city
# and the first day in the next), we can schedule the trip in 10 days.
#
# Available direct flights:
#   • Krakow and Vienna,
#   • Vienna and Riga.
#
# This means the itinerary order is:
#   Krakow -> Vienna -> Riga.
#
# Let:
#   d1 = flight day from Krakow to Vienna.
#   d2 = flight day from Vienna to Riga.
#
# Then the segments are:
#
# 1. Krakow segment:
#    - Runs from Day 1 to Day d1 (duration = d1 days).
#    - Must be 3 days: d1 == 3.
#
# 2. Vienna segment:
#    - Runs from Day d1 to Day d2 (duration = d2 - d1 + 1 days).
#    - Must be 2 days: d2 - d1 + 1 == 2.
#
# 3. Riga segment:
#    - Runs from Day d2 to Day 10 (duration = 10 - d2 + 1 days).
#    - Must be 7 days: 10 - d2 + 1 == 7.
#
# Note: The Riga segment (Days 4 to 10) ensures the annual show in Riga is attended.
# From the equation for the Riga segment, we get: 11 - d2 == 7, hence d2 = 4.
#
# Now we model these constraints using the Z3 solver.

s = Solver()

# Flight day variables:
d1 = Int('d1')  # Flight day from Krakow to Vienna.
d2 = Int('d2')  # Flight day from Vienna to Riga.

# Constraint for the Krakow segment: 3 days.
s.add(d1 == 3)

# Constraint for the Vienna segment: 2 days.
s.add(d2 - d1 + 1 == 2)

# Constraint for the Riga segment: 7 days.
s.add(10 - d2 + 1 == 7)

# Enforce ordering and valid day boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 10)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 3 (flight from Krakow to Vienna on Day 3)
    d2_val = m[d2].as_long()  # Expected: 4 (flight from Vienna to Riga on Day 4)
    
    print("Trip plan found:\n")
    
    # Krakow segment.
    print("1. Stay in Krakow from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Krakow to Vienna.".format(d1_val))
    
    # Vienna segment.
    print("2. Stay in Vienna from Day {} to Day {} (2 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Vienna to Riga.".format(d2_val))
    
    # Riga segment.
    print("3. Stay in Riga from Day {} to Day 10 (7 days).".format(d2_val))
    print("   -> Attend the annual show in Riga from Day 4 to Day 10.")
else:
    print("No solution exists!")