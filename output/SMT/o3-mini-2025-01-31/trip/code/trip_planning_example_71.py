from z3 import *

# We have a 15-day trip visiting 3 European cities with the following requirements:
#   • Rome: 7 days.
#   • London: 7 days.
#   • Krakow: 3 days, and the annual show in Krakow takes place from Day 13 to Day 15.
#
# The sum of stays would be 7 + 7 + 3 = 17 days, but overlapping flight days let the trip fit in 15 days.
#
# The available direct flights are:
#   • between Rome and London,
#   • between London and Krakow.
#
# We choose the itinerary order:
#   Rome -> London -> Krakow
#
# We adopt the convention that when taking a direct flight on a day,
# that day counts as the last day at the departing city and the first day at the arriving city.
#
# Let:
#   d1 = flight day from Rome to London.
#   d2 = flight day from London to Krakow.
#
# The segments are as follows:
#
# 1. Rome segment:
#    Runs from Day 1 to Day d1.
#    Duration = d1 days.
#    Since Rome must be 7 days, we set d1 = 7.
#
# 2. London segment:
#    Runs from Day d1 to Day d2.
#    Duration = d2 - d1 + 1 days.
#    London must be 7 days, so: d2 - d1 + 1 = 7.
#    With d1 = 7, this gives: d2 = 13.
#
# 3. Krakow segment:
#    Runs from Day d2 to Day 15.
#    Duration = 15 - d2 + 1 days.
#    Krakow must be 3 days, so: 15 - d2 + 1 = 3.
#    With d2 = 13, we have: 15 - 13 + 1 = 3.
#
# This itinerary also places the Krakow segment exactly from Day 13 to Day 15,
# meeting the requirement of attending the annual show in Krakow.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Rome to London.
d2 = Int('d2')  # Flight day from London to Krakow.

# Rome segment must last 7 days:
s.add(d1 == 7)

# London segment must last 7 days: d2 - d1 + 1 = 7 ==> d2 = d1 + 6 = 13.
s.add(d2 - d1 + 1 == 7)

# Krakow segment must last 3 days: 15 - d2 + 1 = 3 ==> d2 = 13.
s.add(15 - d2 + 1 == 3)

# Enforce flight ordering and valid day boundaries:
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 15)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 7 (Rome -> London flight)
    d2_val = m[d2].as_long()  # Expected to be 13 (London -> Krakow flight)
    
    print("Trip plan found:\n")
    
    # Rome segment.
    print("1. Stay in Rome from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Rome to London.".format(d1_val))
    
    # London segment.
    print("2. Stay in London from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from London to Krakow.".format(d2_val))
    
    # Krakow segment.
    print("3. Stay in Krakow from Day {} to Day 15 (3 days).".format(d2_val))
    print("   -> Attend the annual show in Krakow from Day 13 to Day 15.")
else:
    print("No solution exists!")