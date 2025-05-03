from z3 import *

# We have a trip of 8 days and 3 cities with available direct flights:
#   - London to Bucharest
#   - Bucharest to Riga
#
# Itinerary requirements:
#   • London: 3 days.
#   • Bucharest: 3 days.
#   • Riga: 4 days.
#
# Additionally, you must attend a workshop in Riga between day 5 and day 8.
#
# We define two flight days:
#    d1: the day when you fly from London to Bucharest.
#        • You are in London from day 1 to day d1.
#
#    d2: the day when you fly from Bucharest to Riga.
#        • You are in Bucharest from day d1 to day d2.
#        • You are in Riga from day d2 to day 8.
#
# When counting durations, the flight day counts in both cities.
#
# Therefore, the durations are:
#   London duration = d1      -> must equal 3.
#   Bucharest duration = d2 - d1 + 1 -> must equal 3.
#   Riga duration = (8 - d2 + 1) = 9 - d2 -> must equal 4.
#
# Also, because you need to attend the workshop in Riga between day 5 and day 8,
# the Riga leg must include day 5. In other words, you must be in Riga by day 5,
# so we require d2 <= 5.
#
# Solving the constraints:
#   From London:       d1 = 3.
#   From Riga:         9 - d2 = 4  -->  d2 = 5.
#   From Bucharest:      d2 - d1 + 1 = 5 - 3 + 1 = 3.
#
# This gives the itinerary:
#   London:    Days 1 to 3 (3 days)
#   Bucharest: Days 3 to 5 (3 days)
#   Riga:      Days 5 to 8 (4 days) -- workshop can be attended from day 5 to 8.
#
# Now we encode these constraints with Z3:

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from London to Bucharest.
d2 = Int('d2')  # Flight day from Bucharest to Riga.

# Add constraints based on the durations:
s.add(d1 == 3)               # London must be 3 days long.
s.add(d2 - d1 + 1 == 3)        # Bucharest must be 3 days long.
s.add(9 - d2 == 4)            # Riga must be 4 days long.

# Enforce flight order and within-trip day bounds:
s.add(d1 < d2)              # Must fly from London to Bucharest before flying to Riga.
s.add(d1 >= 1, d2 <= 8)       # Flight days must be within the 8-day trip.

# Ensure that the Riga leg covers the workshop window:
# Since Riga is visited from day d2 to day 8, d2 must be <= 5 to guarantee presence
# during day 5.
s.add(d2 <= 5)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Should be 3
    d2_val = m[d2].as_long()  # Should be 5

    print("Trip plan found:\n")
    print("1. Stay in London from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from London to Bucharest.".format(d1_val))
    print("2. Stay in Bucharest from Day {} to Day {} (3 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Bucharest to Riga.".format(d2_val))
    print("3. Stay in Riga from Day {} to Day 8 (4 days).".format(d2_val))
    print("   -> Attend the workshop in Riga between Day 5 and Day 8.")
else:
    print("No solution exists!")