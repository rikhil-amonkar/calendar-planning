from z3 import *

# We have a 15-day trip visiting 3 cities with the following requirements:
#   • Naples: 6 days.
#   • Berlin: 7 days.
#   • Krakow: 4 days, with a meeting with friends in Krakow scheduled between Day 12 and Day 15.
#
# Without overlapping, the total would be 6 + 7 + 4 = 17 days.
# By overlapping flight days (each flight day counts as the last day in one city 
# and the first day in the next), we can compress the schedule into 15 days.
#
# The available direct flights:
#   • between Naples and Berlin,
#   • between Berlin and Krakow.
#
# This fixes the itinerary order as:
#   Naples -> Berlin -> Krakow.
#
# Let:
#   d1 = flight day from Naples to Berlin.
#   d2 = flight day from Berlin to Krakow.
#
# Then the segments are defined as:
#
# 1. Naples segment:
#    - Days 1 to d1 (inclusive); Duration = d1 days.
#    - Must equal 6 days: d1 == 6.
#
# 2. Berlin segment:
#    - Days d1 to d2 (inclusive); Duration = d2 - d1 + 1.
#    - Must equal 7 days: d2 - d1 + 1 == 7.
#
# 3. Krakow segment:
#    - Days d2 to 15 (inclusive); Duration = 15 - d2 + 1.
#    - Must equal 4 days: 15 - d2 + 1 == 4  =>  16 - d2 == 4  =>  d2 == 12.
#
# Note: The Krakow segment (from Day 12 to Day 15) aligns with meeting your friends there between Day 12 and Day 15.
#
# Now we model these constraints using the Z3 solver.

s = Solver()

# Define the flight day variables:
d1 = Int('d1')  # Flight day from Naples to Berlin.
d2 = Int('d2')  # Flight day from Berlin to Krakow.

# Naples segment: must be 6 days.
s.add(d1 == 6)

# Berlin segment: must be 7 days.
s.add(d2 - d1 + 1 == 7)

# Krakow segment: must be 4 days.
s.add(15 - d2 + 1 == 4)

# Enforce ordering: flight from Naples to Berlin happens before the flight from Berlin to Krakow.
s.add(d1 < d2)

# Ensure the flight days are within the 15-day itinerary.
s.add(d1 >= 1, d2 <= 15)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 6 (flight from Naples to Berlin on Day 6)
    d2_val = m[d2].as_long()  # Expected: 12 (flight from Berlin to Krakow on Day 12)
    
    print("Trip plan found:\n")
    
    # Naples segment.
    print("1. Stay in Naples from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Naples to Berlin.".format(d1_val))
    
    # Berlin segment.
    print("2. Stay in Berlin from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Berlin to Krakow.".format(d2_val))
    
    # Krakow segment.
    print("3. Stay in Krakow from Day {} to Day 15 (4 days).".format(d2_val))
    print("   -> Meet your friends in Krakow between Day 12 and Day 15 for the tour.")
else:
    print("No solution exists!")