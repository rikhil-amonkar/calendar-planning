from z3 import *

# We have a 14-day trip and 3 cities with the following direct flights:
#   • Istanbul and Amsterdam have a direct flight.
#   • Amsterdam and Santorini have a direct flight.
#
# Itinerary requirements:
#   - Visit Istanbul for 6 days.
#   - Stay in Amsterdam for 7 days.
#   - Visit Santorini for 3 days.
#
# Additional constraint:
#   - You plan to visit relatives in Santorini between day 12 and day 14,
#     so your time in Santorini must include that period.
#
# We model the itinerary with two flight days:
#   d1: the day you fly from Istanbul to Amsterdam.
#       You are in Istanbul from Day 1 to Day d1 (inclusive).
#
#   d2: the day you fly from Amsterdam to Santorini.
#       You are in Amsterdam from Day d1 to Day d2 (inclusive),
#       and in Santorini from Day d2 to Day 14.
#
# Note: The flight day counts in both the city you leave and the city you enter.
#
# Durations (using inclusive counting):
#   Istanbul duration = d1 must equal 6.
#   Amsterdam duration = d2 - d1 + 1 must equal 7.
#   Santorini duration = 14 - d2 + 1 = 15 - d2 must equal 3.
#
# From Santorini constraint: 15 - d2 = 3  ->  d2 = 12.
# Then Amsterdam constraint becomes: 12 - d1 + 1 = 7  ->  13 - d1 = 7  ->  d1 = 6.
#
# This gives the itinerary:
#   - Istanbul: Day 1 to Day 6 (6 days).
#   - Amsterdam: Day 6 to Day 12 (7 days).
#   - Santorini: Day 12 to Day 14 (3 days), which covers the relatives visit from Day 12 to 14.
#
# Now we encode these constraints using Z3.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Istanbul to Amsterdam.
d2 = Int('d2')  # Flight day from Amsterdam to Santorini.

# Add constraints for durations:
s.add(d1 == 6)          # Istanbul for 6 days (days 1 to 6).
s.add(d2 - d1 + 1 == 7)   # Amsterdam for 7 days.
s.add(15 - d2 == 3)       # Santorini for 3 days.

# Enforce flight order and overall schedule limits:
s.add(d1 < d2)           # Must fly to Amsterdam before Santorini.
s.add(d1 >= 1, d2 <= 14)   # Flight days must be within the trip (day 1 to day 14).

# Ensure that Santorini stay covers the relatives' visit window (days 12 to 14)
# Since Santorini is visited from day d2 to day 14, we require d2 <= 12.
s.add(d2 <= 12)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 6.
    d2_val = m[d2].as_long()  # Expected to be 12.

    print("Trip plan found:\n")
    print("1. Stay in Istanbul from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Istanbul to Amsterdam.".format(d1_val))
    print("2. Stay in Amsterdam from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Amsterdam to Santorini.".format(d2_val))
    print("3. Stay in Santorini from Day {} to Day 14 (3 days).".format(d2_val))
    print("   -> Visit your relatives in Santorini between Day 12 and Day 14.")
else:
    print("No solution exists!")