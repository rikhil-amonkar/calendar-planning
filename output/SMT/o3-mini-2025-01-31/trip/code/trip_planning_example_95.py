from z3 import *

# We have a 12-day trip visiting 3 cities with the following requirements:
#   • Dublin: 6 days (and you will attend a wedding there between Day 1 and Day 6).
#   • Vienna: 5 days.
#   • Vilnius: 3 days.
#
# Without overlapping, the total would be 6 + 5 + 3 = 14 days.
# By overlapping flight days (each flight day counts as both the last day in one city
# and the first day in the next), we can compress the schedule into 12 days.
#
# Available direct flights:
#   • between Dublin and Vienna,
#   • between Vienna and Vilnius.
#
# This leads to the itinerary order:
#   Dublin -> Vienna -> Vilnius.
#
# Let:
#   d1 = flight day from Dublin to Vienna.
#   d2 = flight day from Vienna to Vilnius.
#
# The segments are then defined as follows:
#
# 1. Dublin segment:
#    - Runs from Day 1 to Day d1, inclusive.
#    - Duration: d1 days.
#    - Must equal 6 days: d1 == 6.
#
# 2. Vienna segment:
#    - Runs from Day d1 to Day d2, inclusive.
#    - Duration: (d2 - d1 + 1) days.
#    - Must equal 5 days: d2 - d1 + 1 == 5.
#
# 3. Vilnius segment:
#    - Runs from Day d2 to Day 12, inclusive.
#    - Duration: (12 - d2 + 1) days.
#    - Must equal 3 days: 12 - d2 + 1 == 3.
#
# Note: The wedding in Dublin between Day 1 and Day 6 will occur while in Dublin.
#
# Now we model these constraints using the Z3 solver.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Dublin to Vienna.
d2 = Int('d2')  # Flight day from Vienna to Vilnius.

# Dublin segment: 6 days.
s.add(d1 == 6)

# Vienna segment: 5 days.
s.add(d2 - d1 + 1 == 5)

# Vilnius segment: 3 days.
s.add(12 - d2 + 1 == 3)

# Enforce ordering: the flight from Dublin to Vienna must happen before the flight to Vilnius.
s.add(d1 < d2)

# Also enforce that these flight days lie within the 12-day itinerary.
s.add(d1 >= 1, d2 <= 12)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 6 (flight from Dublin to Vienna on Day 6)
    d2_val = m[d2].as_long()  # Expected to be 10 (flight from Vienna to Vilnius on Day 10)
    
    print("Trip plan found:\n")
    
    # Dublin segment.
    print("1. Stay in Dublin from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> Attend the wedding in Dublin between Day 1 and Day 6.")
    print("   -> On Day {}, take a direct flight from Dublin to Vienna.".format(d1_val))
    
    # Vienna segment.
    print("2. Stay in Vienna from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Vienna to Vilnius.".format(d2_val))
    
    # Vilnius segment.
    print("3. Stay in Vilnius from Day {} to Day 12 (3 days).".format(d2_val))
else:
    print("No solution exists!")