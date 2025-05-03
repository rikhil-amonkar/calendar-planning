from z3 import *

# In this problem, the available direct flights connect:
#   • Prague and Vienna
#   • Vienna and Porto
#
# This forces an itinerary order of:
#   Prague -> Vienna -> Porto
#
# The trip lasts 9 days. We introduce:
#   d1: the flight day from Prague to Vienna.
#       Thus, Prague is visited from Day 1 to Day d1.
#   d2: the flight day from Vienna to Porto.
#       Thus, Vienna is visited from Day d1 to Day d2, and Porto from Day d2 to Day 9.
#
# We assume that the travel day is counted for both cities.
#
# The requirements are:
#   1. Stay in Prague for 3 days.
#      => Duration in Prague = d1 days, so d1 == 3.
#
#   2. Attend a workshop in Prague between Day 1 and Day 3.
#      => With Prague from Day 1 to Day 3, this condition is met.
#
#   3. Stay in Vienna for 3 days.
#      => Duration in Vienna = (d2 - d1 + 1) days, so d2 - d1 + 1 == 3.
#
#   4. Stay in Porto for 5 days.
#      => Duration in Porto = (9 - d2 + 1) = 10 - d2 days, so 10 - d2 == 5.
#
# Let’s solve these:

s = Solver()

# Define the flight switching day variables.
d1 = Int('d1')  # Flight from Prague to Vienna.
d2 = Int('d2')  # Flight from Vienna to Porto.

# Add constraints to satisfy durations:
s.add(d1 == 3)                     # Prague must be 3 days: Days 1 to 3.
s.add(d2 - d1 + 1 == 3)              # Vienna must be 3 days.
s.add(10 - d2 == 5)                  # Porto must be 5 days.

# Enforce timing order and bounds:
s.add(d1 < d2)          # Trip order: flight from Prague->Vienna happens before Vienna->Porto.
s.add(d1 >= 1, d2 <= 9)   # Flight days must fall within the overall 9-day trip.

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # expected to be 3
    d2_val = model[d2].as_long()  # expected to be 5
    
    print("Trip plan found:\n")
    print("1. Stay in Prague from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> Attend the workshop in Prague between Day 1 and Day 3.")
    print("   -> On Day {}, take a direct flight from Prague to Vienna.".format(d1_val))
    print("2. Stay in Vienna from Day {} to Day {} (3 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Vienna to Porto.".format(d2_val))
    print("3. Stay in Porto from Day {} to Day 9 (5 days).".format(d2_val))
else:
    print("No solution exists!")