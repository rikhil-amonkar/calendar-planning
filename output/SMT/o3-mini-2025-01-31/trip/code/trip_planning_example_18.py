from z3 import *

# In this problem, we have 3 cities:
#   • Vilnius (2 days)
#   • Amsterdam (5 days)
#   • Bucharest (6 days, with a meet-up between day 6 and day 11)
#
# The available direct flights are:
#   • Vilnius <-> Amsterdam
#   • Amsterdam <-> Bucharest
#
# That forces a valid itinerary order of:
#   Vilnius -> Amsterdam -> Bucharest
#
# We define:
#   d1: the day when you take the flight from Vilnius to Amsterdam.
#       You are in Vilnius from Day 1 to Day d1 (inclusive).
#
#   d2: the day when you take the flight from Amsterdam to Bucharest.
#       You are in Amsterdam from Day d1 to Day d2 (inclusive),
#       and you are in Bucharest from Day d2 to Day 11 (inclusive).
#
# The durations must satisfy:
# 1. Vilnius for 2 days: d1 == 2.
# 2. Amsterdam for 5 days: duration = d2 - d1 + 1, so d2 - d1 + 1 == 5.
# 3. Bucharest for 6 days: duration = (11 - d2 + 1) = 12 - d2, so 12 - d2 == 6.
#
# Additionally, you want to meet your friends in Bucharest between day 6 and day 11.
# Given the Bucharest leg starts on day d2 and with d2 computed below, this will be satisfied.
#
# Solving:
#   From (1): d1 = 2.
#   From (3): 12 - d2 == 6  -> d2 = 6.
#   Then check Amsterdam's duration: 6 - 2 + 1 = 5, which satisfies the requirement.
#
# Let's encode this in Z3.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Vilnius to Amsterdam.
d2 = Int('d2')  # Flight day from Amsterdam to Bucharest.

# Add the constraints for durations:
s.add(d1 == 2)                   # Vilnius for 2 days: Days 1 to 2.
s.add(d2 - d1 + 1 == 5)            # Amsterdam for 5 days.
s.add(12 - d2 == 6)                # Bucharest for 6 days.

# Enforce the order of flights:
s.add(d1 < d2)                   # Must fly from Vilnius to Amsterdam before going to Bucharest.
s.add(d1 >= 1, d2 <= 11)           # Flight days within overall 11-day trip.

# Check and print the solution:
if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # Expected: 2
    d2_val = model[d2].as_long()  # Expected: 6

    print("Trip plan found:\n")
    print("1. Stay in Vilnius from Day 1 to Day {} (2 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Vilnius to Amsterdam.".format(d1_val))
    print("2. Stay in Amsterdam from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Amsterdam to Bucharest.".format(d2_val))
    print("3. Stay in Bucharest from Day {} to Day 11 (6 days).".format(d2_val))
    print("   -> Meet your friends in Bucharest between Day 6 and Day 11.")
else:
    print("No solution exists!")