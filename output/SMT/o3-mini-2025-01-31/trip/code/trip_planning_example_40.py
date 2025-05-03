from z3 import *

# We plan an 8-day trip visiting 3 cities with the following requirements:
#   • Manchester: 2 days (with a wedding to attend between Day 1 and Day 2).
#   • Oslo:      6 days.
#   • Reykjavik: 2 days.
#
# The available direct flights are:
#   • between Manchester and Oslo,
#   • between Oslo and Reykjavik.
#
# We assume the following itinerary:
#   Manchester -> Oslo -> Reykjavik.
#
# We use the convention that when you take a flight on a day, that day counts as both the last day in 
# the departure city and the first day in the arrival city.
#
# Let:
#   d1 = the flight day from Manchester to Oslo.
#   d2 = the flight day from Oslo to Reykjavik.
#
# Then, the segments are modeled as:
#   Manchester: Days 1 to d1,        duration = d1 days (should equal 2 days).
#   Oslo:      Days d1 to d2,         duration = d2 - d1 + 1 days (should equal 6 days).
#   Reykjavik: Days d2 to Day 8,        duration = 8 - d2 + 1 = 9 - d2 days (should equal 2 days).
#
# The constraints become:
#   1. d1 == 2            (Manchester: 2 days; wedding is attended between Day 1 and Day 2).
#   2. d2 - d1 + 1 == 6   (Oslo: 6 days).
#   3. 9 - d2 == 2        (Reykjavik: 2 days).
#
# This yields:
#   d1 = 2,
#   d2 - 2 + 1 = 6  => d2 = 7,
#   9 - 7 = 2.
#
# The flight days satisfy 1 <= d1 < d2 <= 8.
#
# Now we encode this problem and solve it using Z3.

# Create a Z3 solver instance.
s = Solver()

# Define flight day variables.
d1 = Int('d1')  # Flight day from Manchester to Oslo.
d2 = Int('d2')  # Flight day from Oslo to Reykjavik.

# Add constraints for each segment.
s.add(d1 == 2)              # Manchester stay is 2 days: Day 1 to Day 2.
s.add(d2 - d1 + 1 == 6)       # Oslo's duration is 6 days.
s.add(9 - d2 == 2)            # Reykjavik's duration is 2 days.

# Enforce flight order and ensure flights occur within the 8-day trip.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 8)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 2
    d2_val = m[d2].as_long()  # Expected: 7

    print("Trip plan found:\n")
    print("1. Stay in Manchester from Day 1 to Day {} (2 days).".format(d1_val))
    print("   -> Attend the wedding in Manchester between Day 1 and Day 2.")
    print("   -> On Day {}, take a direct flight from Manchester to Oslo.".format(d1_val))
    print("2. Stay in Oslo from Day {} to Day {} (6 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Oslo to Reykjavik.".format(d2_val))
    print("3. Stay in Reykjavik from Day {} to Day 8 (2 days).".format(d2_val))
else:
    print("No solution exists!")