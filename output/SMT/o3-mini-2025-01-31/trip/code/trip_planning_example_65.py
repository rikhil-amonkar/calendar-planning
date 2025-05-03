from z3 import *

# We have a 12-day trip visiting 3 European cities with the following requirements:
#   • Mykonos: 4 days.
#   • Milan: 3 days.
#   • Santorini: 7 days, with a required visit to relatives in Santorini between Day 6 and Day 12.
#
# Although the sum of days is 4 + 3 + 7 = 14, by overlapping on the flight days,
# the trip fits exactly into 12 days.
#
# The available direct flights are:
#   • between Mykonos and Milan,
#   • between Milan and Santorini.
#
# We choose the itinerary order:
#   Mykonos -> Milan -> Santorini
#
# We adopt the convention that when you take a direct flight on a day,
# that day counts as both the last day at the departing city and the first day at the arriving city.
#
# Let:
#   d1 = flight day from Mykonos to Milan.
#   d2 = flight day from Milan to Santorini.
#
# Then, the segments are as follows:
#
# 1. Mykonos segment:
#    Runs from Day 1 to Day d1.
#    Duration = d1 days.
#    Required duration: 4 days, so we set d1 = 4.
#
# 2. Milan segment:
#    Runs from Day d1 to Day d2.
#    Duration = d2 - d1 + 1 days.
#    Required duration: 3 days, so: d2 - d1 + 1 = 3.
#    With d1 = 4, this implies: d2 = 6.
#
# 3. Santorini segment:
#    Runs from Day d2 to Day 12.
#    Duration = 12 - d2 + 1 days.
#    Required duration: 7 days, so: 12 - d2 + 1 = 7.
#    With d2 = 6, we get: 12 - 6 + 1 = 7.
#
# The Santorini segment (Day 6 to Day 12) naturally covers the relatives visit requirement.
#
# This itinerary meets all the requirements.
s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Mykonos to Milan.
d2 = Int('d2')  # Flight day from Milan to Santorini.

# Mykonos segment: must last 4 days.
# Duration = d1 days since trip starts at Day 1, therefore:
s.add(d1 == 4)

# Milan segment: must last 3 days.
# Duration = d2 - d1 + 1. Therefore:
s.add(d2 - d1 + 1 == 3)

# Santorini segment: must last 7 days.
# Duration = 12 - d2 + 1, therefore:
s.add(12 - d2 + 1 == 7)

# Enforce flight ordering and valid day boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 12)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 4 (Mykonos -> Milan flight)
    d2_val = m[d2].as_long()  # Expected to be 6 (Milan -> Santorini flight)
    
    print("Trip plan found:\n")
    
    # Mykonos segment.
    print("1. Stay in Mykonos from Day 1 to Day {} (4 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Mykonos to Milan.".format(d1_val))
    
    # Milan segment.
    print("2. Stay in Milan from Day {} to Day {} (3 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Milan to Santorini.".format(d2_val))
    
    # Santorini segment.
    print("3. Stay in Santorini from Day {} to Day 12 (7 days).".format(d2_val))
    print("   -> Visit your relatives in Santorini between Day 6 and Day 12.")
else:
    print("No solution exists!")