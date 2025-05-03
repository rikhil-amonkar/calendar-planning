from z3 import *

# We have a 14-day trip visiting 3 cities with the following requirements:
#   • Santorini: 6 days, and you want to attend the annual show there from Day 1 to Day 6.
#   • London: 5 days.
#   • Krakow: 5 days.
#
# Without overlapping, the total days would be 6 + 5 + 5 = 16 days.
# By overlapping flight days (each flight day counts as the last day in one city
# and simultaneously as the first day in the next), we can compress the itinerary into 14 days.
#
# The available direct flights are:
#   • between Santorini and London,
#   • between London and Krakow.
#
# This determines the itinerary order as:
#   Santorini -> London -> Krakow.
#
# Let:
#   d1 = flight day from Santorini to London.
#   d2 = flight day from London to Krakow.
#
# The segments are defined as follows:
#
# 1. Santorini segment:
#    - Runs from Day 1 to Day d1 (inclusive).
#    - Duration is d1 days.
#    - Must equal 6 days; hence, d1 == 6.
#
# 2. London segment:
#    - Runs from Day d1 to Day d2 (inclusive).
#    - Duration is (d2 - d1 + 1) days.
#    - Must equal 5 days; hence, d2 - d1 + 1 == 5.
#
# 3. Krakow segment:
#    - Runs from Day d2 to Day 14 (inclusive).
#    - Duration is (14 - d2 + 1) days.
#    - Must equal 5 days; hence, 14 - d2 + 1 == 5 => 15 - d2 == 5  =>  d2 == 10.
#
# With these flight days, the Santorini segment covers Day 1 to Day 6,
# matching the schedule for the annual show, the London segment spans Day 6 to Day 10,
# and the Krakow segment spans Day 10 to Day 14.
#
# Now we model these constraints using the Z3 solver.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Santorini to London.
d2 = Int('d2')  # Flight day from London to Krakow.

# Santorini segment: Must be 6 days.
s.add(d1 == 6)

# London segment: Must be 5 days.
s.add(d2 - d1 + 1 == 5)

# Krakow segment: Must be 5 days.
s.add(14 - d2 + 1 == 5)

# Enforce flight order.
s.add(d1 < d2)

# Ensure flight days fall within our 14-day itinerary.
s.add(d1 >= 1, d2 <= 14)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 6
    d2_val = m[d2].as_long()  # Expected to be 10
    
    print("Trip plan found:\n")
    
    # Santorini segment.
    print("1. Stay in Santorini from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> Attend the annual show in Santorini from Day 1 to Day 6.")
    print("   -> On Day {}, take a direct flight from Santorini to London.".format(d1_val))
    
    # London segment.
    print("2. Stay in London from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from London to Krakow.".format(d2_val))
    
    # Krakow segment.
    print("3. Stay in Krakow from Day {} to Day 14 (5 days).".format(d2_val))
else:
    print("No solution exists!")