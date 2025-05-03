from z3 import *

# In this scheduling problem you plan a 12‑day trip visiting 3 cities with the following requirements:
#   • Porto:   3 days and you must visit relatives in Porto between Day 1 and Day 3.
#   • Barcelona: 7 days.
#   • Florence: 4 days.
#
# The available direct flights are:
#   • between Porto and Barcelona,
#   • between Barcelona and Florence.
#
# We assume a flight itinerary:
#   Porto -> Barcelona -> Florence.
#
# We adopt the convention that when you take a flight on a day, that day serves as both the last day
# in the departure city and the first day in the arrival city.
#
# Let:
#   d1 = the flight day from Porto to Barcelona.
#   d2 = the flight day from Barcelona to Florence.
#
# Then, the trip segments are:
#   - Porto:     Days 1 to d1,      duration = d1 days, and we require d1 = 3.
#   - Barcelona: Days d1 to d2,      duration = d2 - d1 + 1 days, and we require d2 - d1 + 1 = 7.
#   - Florence:  Days d2 to Day 12,  duration = 12 - d2 + 1 = 13 - d2 days, and we require 13 - d2 = 4.
#
# Solving the constraints:
#   d1 = 3.
#   d2 - 3 + 1 = 7  => d2 = 9.
#   13 - 9 = 4.
#
# These values ensure the overall trip lasts 12 days (accounting for overlap on flight days)
# and that all conditions are met including the Porto relatives visit (Porto is visited on Days 1-3).

# Create a Z3 solver instance.
s = Solver()

# Define flight day variables.
d1 = Int('d1')  # Flight day from Porto to Barcelona.
d2 = Int('d2')  # Flight day from Barcelona to Florence.

# Add constraints on each period.
s.add(d1 == 3)                 # Porto is visited for exactly 3 days (Days 1 to 3).
s.add(d2 - d1 + 1 == 7)          # Barcelona is visited for exactly 7 days.
s.add(13 - d2 == 4)              # Florence is visited for exactly 4 days.

# Enforce flight order and proper day bounds.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 12)

# Check the constraints and print the plan.
if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 3
    d2_val = m[d2].as_long()  # Expected: 9

    print("Trip plan found:\n")
    print("1. Stay in Porto from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Porto to Barcelona.".format(d1_val))
    print("2. Stay in Barcelona from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Barcelona to Florence.".format(d2_val))
    print("3. Stay in Florence from Day {} to Day 12 (4 days).".format(d2_val))
    print("\nNote: During Days 1 to 3 in Porto, you visit relatives as required.")
else:
    print("No solution exists!")