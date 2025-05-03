from z3 import *

# We have a trip of 11 days visiting 3 cities with the following requirements:
#   • Krakow: 7 days.
#   • London: 3 days.
#   • Lyon: 3 days, with a meeting with friends (tour) scheduled in Lyon between Day 9 and Day 11.
#
# Without overlapping, the total would be: 7 + 3 + 3 = 13 days.
# By overlapping flight days (each flight day counts as the last day in one city
# and the first day in the next city), we can compress the schedule into 11 days.
#
# The available direct flights:
#   • between Krakow and London,
#   • between London and Lyon.
#
# Therefore, the itinerary order is:
#   Krakow -> London -> Lyon.
#
# Let:
#   d1 = flight day from Krakow to London.
#   d2 = flight day from London to Lyon.
#
# The segments:
#
# 1. Krakow segment:
#    - Duration: Day 1 to Day d1 (inclusive), which is d1 days.
#    - Must equal 7 days: d1 == 7.
#
# 2. London segment:
#    - Duration: Day d1 to Day d2 (inclusive), which is d2 - d1 + 1 days.
#    - Must equal 3 days: d2 - d1 + 1 == 3.
#
# 3. Lyon segment:
#    - Duration: Day d2 to Day 11 (inclusive), which is 11 - d2 + 1 = 12 - d2 days.
#    - Must equal 3 days: 12 - d2 == 3, so d2 = 9.
#
# Also, the meeting in Lyon is scheduled between Day 9 and Day 11.
# The Lyon segment runs from Day 9 to Day 11, satisfying that condition.
#
# We now model these constraints using the Z3 solver.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Krakow to London.
d2 = Int('d2')  # Flight day from London to Lyon.

# Constraint for the Krakow segment: 7 days.
s.add(d1 == 7)

# Constraint for the London segment: 3 days.
s.add(d2 - d1 + 1 == 3)

# Constraint for the Lyon segment: 3 days.
s.add(12 - d2 == 3)

# Enforce ordering: flight from Krakow comes before flight from London.
s.add(d1 < d2)

# Valid day ranges: they must fall within the 11-day schedule.
s.add(d1 >= 1, d2 <= 11)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 7 (flight Krakow->London on Day 7)
    d2_val = m[d2].as_long()  # Expected to be 9 (flight London->Lyon on Day 9)
    
    print("Trip plan found:\n")
    
    # Krakow segment.
    print("1. Stay in Krakow from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Krakow to London.".format(d1_val))
    
    # London segment.
    print("2. Stay in London from Day {} to Day {} (3 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from London to Lyon.".format(d2_val))
    
    # Lyon segment.
    print("3. Stay in Lyon from Day {} to Day 11 (3 days).".format(d2_val))
    print("   -> Meet your friends in Lyon between Day 9 and Day 11 for the tour.")
else:
    print("No solution exists!")