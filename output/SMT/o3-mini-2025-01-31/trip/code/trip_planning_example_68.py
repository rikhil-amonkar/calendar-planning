from z3 import *

# We have a 14-day trip visiting 3 European cities with the following requirements:
#   • Reykjavik: 3 days.
#   • Zurich: 6 days.
#   • Porto: 7 days and you must attend a workshop in Porto between Day 8 and Day 14.
#
# The total sum of days is (3 + 6 + 7 = 16) if we added the stays separately,
# but the overlapping flight days allow the trip to fit into 14 days.
#
# The available direct flights are:
#   • between Reykjavik and Zurich,
#   • between Zurich and Porto.
#
# We choose the itinerary order:
#   Reykjavik -> Zurich -> Porto
#
# We adopt the convention that when you take a direct flight on a day,
# that day counts as both the last day at the departing city and the first day at the arriving city.
#
# Let:
#   d1 = flight day from Reykjavik to Zurich.
#   d2 = flight day from Zurich to Porto.
#
# Then the segments are:
#
# 1. Reykjavik segment:
#    Runs from Day 1 to Day d1.
#    Duration = d1 days.
#    Required: 3 days in Reykjavik, so set d1 = 3.
#
# 2. Zurich segment:
#    Runs from Day d1 to Day d2.
#    Duration = d2 - d1 + 1 days.
#    Required: 6 days in Zurich, so: d2 - d1 + 1 = 6.
#    With d1 = 3, we obtain d2 = 3 + 6 - 1 = 8.
#
# 3. Porto segment:
#    Runs from Day d2 to Day 14.
#    Duration = 14 - d2 + 1 days.
#    Required: 7 days in Porto, so: 14 - d2 + 1 = 7.
#    With d2 = 8, we have 14 - 8 + 1 = 7.
#
# The Porto segment (Day 8 to Day 14) meets the workshop requirement (i.e. attending between Day 8 and Day 14).
#
# This itinerary satisfies all requirements.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Reykjavik to Zurich.
d2 = Int('d2')  # Flight day from Zurich to Porto.

# Reykjavik segment must last 3 days:
s.add(d1 == 3)

# Zurich segment must last 6 days:
s.add(d2 - d1 + 1 == 6)

# Porto segment must last 7 days:
s.add(14 - d2 + 1 == 7)

# Enforce flight ordering and day boundaries:
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 14)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()   # Expected: 3 (flight from Reykjavik to Zurich)
    d2_val = m[d2].as_long()   # Expected: 8 (flight from Zurich to Porto)
    
    print("Trip plan found:\n")
    
    # Reykjavik segment.
    print("1. Stay in Reykjavik from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Reykjavik to Zurich.".format(d1_val))
    
    # Zurich segment.
    print("2. Stay in Zurich from Day {} to Day {} (6 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Zurich to Porto.".format(d2_val))
    
    # Porto segment.
    print("3. Stay in Porto from Day {} to Day 14 (7 days).".format(d2_val))
    print("   -> Attend the workshop in Porto between Day 8 and Day 14.")
else:
    print("No solution exists!")