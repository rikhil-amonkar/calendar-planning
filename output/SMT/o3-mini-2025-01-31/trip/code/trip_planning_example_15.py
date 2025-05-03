from z3 import *

# In this scheduling problem, the available direct flights are:
#   • Krakow <-> Berlin
#   • Berlin <-> Porto
#
# This forces a valid itinerary order of:
#   Krakow -> Berlin -> Porto
#
# The trip lasts 11 days. We define:
#   d1: the day you take the direct flight from Krakow to Berlin.
#       Thus, you are in Krakow from Day 1 to Day d1 (inclusive).
#   d2: the day you take the direct flight from Berlin to Porto.
#       Thus, you are in Berlin from Day d1 to Day d2 (inclusive),
#       and in Porto from Day d2 to Day 11 (inclusive).
#
# Note: the travel (flight) days are shared by the two consecutive city visits.
#
# Requirements:
#   1. Stay in Krakow for 5 days.
#      This means the Krakow leg has a duration of d1 days, so we require:
#           d1 == 5
#
#   2. Visit Berlin for 6 days.
#      Berlin leg duration is given by (d2 - d1 + 1), so:
#           d2 - d1 + 1 == 6
#      With d1 fixed to 5, this yields:
#           d2 - 5 + 1 == 6  -> d2 = 10
#
#   3. Stay in Porto for 2 days.
#      Porto leg duration is (11 - d2 + 1) = (12 - d2), so:
#           12 - d2 == 2  -> d2 = 10
#
#   4. You are attending a wedding in Porto between Day 10 and Day 11.
#      Since the Porto leg is from Day d2 to Day 11, and d2 = 10,
#      you will be in Porto exactly on Days 10 and 11.
#
# With these constraints, the itinerary is determined:
#   - Krakow: Day 1 to Day 5 (5 days).
#   - Berlin: Day 5 to Day 10 (6 days).
#   - Porto:  Day 10 to Day 11 (2 days).
#
# Now we set up and solve these constraints using the Z3 solver.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Krakow to Berlin.
d2 = Int('d2')  # Flight day from Berlin to Porto.

# Add constraints based on durations:
s.add(d1 == 5)           # Krakow for 5 days: Days 1 to 5.
s.add(d2 - d1 + 1 == 6)    # Berlin for 6 days.
s.add(12 - d2 == 2)        # Porto for 2 days.

# Enforce timeline ordering and bounds:
s.add(d1 < d2)           # The flight from Krakow to Berlin must occur before Berlin to Porto.
s.add(d1 >= 1, d2 <= 11)   # Flight days must lie within the overall trip duration.

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # expected to be 5
    d2_val = model[d2].as_long()  # expected to be 10

    print("Trip plan found:\n")
    print("1. Stay in Krakow from Day 1 to Day {} (5 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Krakow to Berlin.".format(d1_val))
    print("2. Stay in Berlin from Day {} to Day {} (6 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Berlin to Porto.".format(d2_val))
    print("3. Stay in Porto from Day {} to Day 11 (2 days).".format(d2_val))
    print("   -> Attend the wedding in Porto between Day 10 and Day 11.")
else:
    print("No solution exists!")