from z3 import *

# We have 3 cities: Vilnius, Vienna, and Valencia.
# Available direct flights:
#   - From Vilnius to Vienna
#   - From Vienna to Valencia
#
# Thus a valid itinerary order is: Vilnius -> Vienna -> Valencia.
#
# The itinerary is over 15 days. We assume the following convention:
#   • Vilnius leg: days 1 to d1 (inclusive)
#   • Vienna leg: days d1 to d2 (inclusive)
#   • Valencia leg: days d2 to 15 (inclusive)
#
# Note that the flight day is shared by both cities (i.e. the day of travel counts as the last day for the departing city and the first day for the arriving city).
#
# The duration requirements are:
#   • Vilnius: 5 days  => d1 == 5
#   • Vienna:  5 days  => (d2 - d1 + 1) == 5
#   • Valencia: 7 days  => (15 - d2 + 1) == 7   (i.e., 16 - d2 == 7)
#
# Additionally, you must attend a conference in Valencia on Day 9 and Day 15.
# If Valencia is from day d2 to day 15, then with d2 determined by the above constraints,
# day 9 and day 15 will fall into the Valencia leg.
#
# Let's set up and solve these constraints with Z3.

s = Solver()

# Define flight switching day variables:
d1 = Int('d1')  # Flight day from Vilnius to Vienna (last day in Vilnius, first day in Vienna)
d2 = Int('d2')  # Flight day from Vienna to Valencia (last day in Vienna, first day in Valencia)

# Add constraints based on duration requirements:
s.add(d1 == 5)                         # Vilnius leg is 5 days: days 1 to 5.
s.add(d2 - d1 + 1 == 5)                  # Vienna leg is 5 days.
s.add(16 - d2 == 7)                      # Valencia leg is 7 days: 16 - d2 = 7  -> d2 = 9

# Enforce the timeline order:
s.add(d1 < d2)         # Must fly from Vilnius to Vienna before Vienna to Valencia.
s.add(d1 >= 1, d2 <= 15)

# Check that the conference days in Valencia (day 9 and day 15) are within the Valencia leg.
# Valencia leg is from d2 to 15. With d2 = 9, both days 9 and 15 are included.
# So no extra constraint is needed beyond what we already have.

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # d1 should be 5 (Vilnius leg ends)
    d2_val = model[d2].as_long()  # d2 should be 9 (Vienna leg ends, Valencia starts)
    
    print("Trip plan found:\n")
    print("1. Stay in Vilnius from Day 1 to Day {} (5 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Vilnius to Vienna.".format(d1_val))
    print("2. Stay in Vienna from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Vienna to Valencia.".format(d2_val))
    print("3. Stay in Valencia from Day {} to Day 15 (7 days).".format(d2_val))
    print("   -> Attend the conference in Valencia on Day 9 and Day 15.")
else:
    print("No solution exists!")