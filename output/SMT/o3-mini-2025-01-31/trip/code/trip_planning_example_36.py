from z3 import *

# In this problem, we plan a 13‑day trip visiting three cities with the following requirements:
#   • Florence: 2 days.
#   • Munich:   6 days.
#   • Warsaw:   7 days.
#
# The available direct flights are:
#   • from Florence to Munich,
#   • from Munich to Warsaw.
#
# We use the common convention that the flight day counts as the last day in the departing city 
# and the first day in the arriving city. If we let:
#   d1 = the flight day from Florence to Munich,
#   d2 = the flight day from Munich to Warsaw,
#
# then the time spent in each city is modeled by:
#
#   Florence: Days 1 to d1,            duration = d1 days.
#   Munich:   Days d1 to d2,            duration = d2 - d1 + 1 days.
#   Warsaw:   Days d2 to Day 13,          duration = 13 - d2 + 1 = 14 - d2 days.
#
# We want:
#   Florence: d1         = 2,
#   Munich:   d2 - d1 + 1 = 6  --> d2 - 2 + 1 = 6  --> d2 = 7,
#   Warsaw:   14 - d2     = 7  --> 14 - 7 = 7.
#
# These equations ensure that the sum of durations (with the overlap on the flight days taken into account)
# equals the total trip length of 13 days. The flight sequence is: Florence -> Munich -> Warsaw.

# Create a Z3 solver instance.
s = Solver()

# Define integer variables for the flight days.
d1 = Int('d1')  # Flight day from Florence to Munich.
d2 = Int('d2')  # Flight day from Munich to Warsaw.

# Add constraints for the city durations.
s.add(d1 == 2)                 # Florence must be visited for 2 days (Days 1 to 2).
s.add(d2 - d1 + 1 == 6)          # Munich must be visited for 6 days.
s.add(14 - d2 == 7)              # Warsaw must be visited for 7 days.

# Ensure the flights occur in proper order and within the overall 13-day schedule.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 13)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 2
    d2_val = m[d2].as_long()  # Expected: 7

    print("Trip plan found:\n")
    print("1. Stay in Florence from Day 1 to Day {} (2 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Florence to Munich.".format(d1_val))
    print("2. Stay in Munich from Day {} to Day {} (6 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Munich to Warsaw.".format(d2_val))
    print("3. Stay in Warsaw from Day {} to Day 13 (7 days).".format(d2_val))
else:
    print("No solution exists!")