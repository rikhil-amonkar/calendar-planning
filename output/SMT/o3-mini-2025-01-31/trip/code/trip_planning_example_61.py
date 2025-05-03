from z3 import *

# We have a 13-day trip visiting 3 European cities.
# The requirements are:
#   • Helsinki: 5 days, and you want to meet your friends in Helsinki between Day 1 and Day 5.
#   • Zurich: 7 days.
#   • Bucharest: 3 days.
#
# Note: Although the sum of days in each city is 5 + 7 + 3 = 15,
# the overlap from shared flight days (when you travel, that day counts in both segments)
# allows the trip to fit in 13 days total.
#
# The available direct flights are:
#   • between Zurich and Bucharest,
#   • between Helsinki and Zurich.
#
# We choose the itinerary order:
#   Helsinki -> Zurich -> Bucharest
#
# We adopt the convention that when you take a direct flight on a day,
# that day counts as both the last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Helsinki to Zurich.
#   d2 = flight day from Zurich to Bucharest.
#
# Then the segments are:
#
# 1. Helsinki segment:
#    From Day 1 to Day d1, the duration is d1 days.
#    We require 5 days in Helsinki, so: d1 = 5.
#    This also guarantees that your meeting with friends in Helsinki takes place
#    within Day 1 and Day 5.
#
# 2. Zurich segment:
#    From Day d1 to Day d2, the duration is (d2 - d1 + 1) days.
#    We require 7 days in Zurich, so: d2 - d1 + 1 = 7.
#    With d1 = 5 this gives: d2 = 11.
#
# 3. Bucharest segment:
#    From Day d2 to Day 13, the duration is (13 - d2 + 1) days.
#    We require 3 days in Bucharest, so: 13 - d2 + 1 = 3.
#    With d2 = 11 this checks: 13 - 11 + 1 = 3.
#
# This itinerary meets all scheduling and flight connection requirements.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Helsinki to Zurich.
d2 = Int('d2')  # Flight day from Zurich to Bucharest.

# Helsinki segment: must last 5 days
s.add(d1 == 5)

# Zurich segment: must last 7 days -> d2 - d1 + 1 = 7
s.add(d2 - d1 + 1 == 7)

# Bucharest segment: must last 3 days -> 13 - d2 + 1 = 3
s.add(13 - d2 + 1 == 3)

# Enforce flight ordering and valid boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 13)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 5 (flight from Helsinki to Zurich)
    d2_val = m[d2].as_long()  # Expected: 11 (flight from Zurich to Bucharest)
    
    print("Trip plan found:\n")
    
    # Helsinki segment.
    print("1. Stay in Helsinki from Day 1 to Day {} (5 days).".format(d1_val))
    print("   -> Meet your friends in Helsinki between Day 1 and Day 5.")
    print("   -> On Day {}, take a direct flight from Helsinki to Zurich.".format(d1_val))
    
    # Zurich segment.
    print("2. Stay in Zurich from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Zurich to Bucharest.".format(d2_val))
    
    # Bucharest segment.
    print("3. Stay in Bucharest from Day {} to Day 13 (3 days).".format(d2_val))
else:
    print("No solution exists!")