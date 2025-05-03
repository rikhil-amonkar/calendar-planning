from z3 import *

# We plan an 11‑day trip visiting 3 cities with the following requirements:
#   • Paris:   4 days, and you want to meet your friends in Paris between Day 1 and Day 4.
#   • Nice:    5 days.
#   • Mykonos: 4 days.
#
# The available direct flights are:
#   • between Paris and Nice,
#   • between Nice and Mykonos.
#
# We assume the itinerary is:
#   Paris -> Nice -> Mykonos.
#
# Using the convention that when you take a flight on a day, that day counts as the last day in the
# departing city and as the first day in the arrival city, we define:
#
# Let:
#   d1 = the flight day from Paris to Nice.
#   d2 = the flight day from Nice to Mykonos.
#
# Then the segments are:
#   - Paris:   Days 1 to d1,           duration = d1 days, which must equal 4.
#   - Nice:    Days d1 to d2,           duration = d2 - d1 + 1 days, which must equal 5.
#   - Mykonos: Days d2 to Day 11,       duration = 11 - d2 + 1 = 12 - d2 days, which must equal 4.
#
# The constraints can be written as:
#   1. d1 == 4.
#   2. d2 - d1 + 1 == 5  -->  d2 - 4 + 1 == 5  -->  d2 = 8.
#   3. 12 - d2 == 4      -->  d2 = 8.
#
# This yields:
#   d1 = 4, and d2 = 8.
#
# With these values:
#   - You spend Days 1-4 in Paris (meeting your friends between Day 1 and Day 4).
#   - You spend Days 4-8 in Nice.
#   - You spend Days 8-11 in Mykonos.
#
# We now encode these constraints and solve them using Z3.

s = Solver()

# Flight day variables:
d1 = Int('d1')  # Flight day from Paris to Nice.
d2 = Int('d2')  # Flight day from Nice to Mykonos.

# Add constraints:
s.add(d1 == 4)               # Paris is visited for 4 days: Days 1 to 4.
s.add(d2 - d1 + 1 == 5)        # Nice is visited for 5 days.
s.add(12 - d2 == 4)            # Mykonos is visited for 4 days.

# Ensure flight order and that flight days fall within the 11-day trip.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 11)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 4
    d2_val = m[d2].as_long()  # Expected: 8

    print("Trip plan found:\n")
    print("1. Stay in Paris from Day 1 to Day {} (4 days).".format(d1_val))
    print("   -> Meet your friends in Paris between Day 1 and Day 4.")
    print("   -> On Day {}, take a direct flight from Paris to Nice.".format(d1_val))
    print("2. Stay in Nice from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Nice to Mykonos.".format(d2_val))
    print("3. Stay in Mykonos from Day {} to Day 11 (4 days).".format(d2_val))
else:
    print("No solution exists!")