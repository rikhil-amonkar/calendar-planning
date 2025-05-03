from z3 import *

# We have a 12-day trip visiting 3 cities with the following requirements:
#   • Dublin: 2 days.
#   • Riga: 5 days.
#   • Vilnius: 7 days.
#
# Without overlapping, the total would be 2 + 5 + 7 = 14 days.
# By overlapping flight days (each flight day counts as both the last day in one city
# and the first day in the next), we can fit the trip in 12 days.
#
# Available direct flights:
#   • between Dublin and Riga,
#   • from Riga to Vilnius.
#
# Therefore, the itinerary order is:
#   Dublin -> Riga -> Vilnius.
#
# Let:
#   d1 = flight day from Dublin to Riga.
#   d2 = flight day from Riga to Vilnius.
#
# Then the segments are:
#
# 1. Dublin segment:
#    - Runs from Day 1 to Day d1.
#    - Duration = d1 days.
#    - Must be 2 days: d1 == 2.
#
# 2. Riga segment:
#    - Runs from Day d1 to Day d2.
#    - Duration = d2 - d1 + 1 days.
#    - Must be 5 days: d2 - d1 + 1 == 5.
#
# 3. Vilnius segment:
#    - Runs from Day d2 to Day 12.
#    - Duration = 12 - d2 + 1 days.
#    - Must be 7 days: 12 - d2 + 1 == 7.
#
# Now we model these constraints using the Z3 solver.

s = Solver()

# Flight day variables:
d1 = Int('d1')  # Flight day from Dublin to Riga.
d2 = Int('d2')  # Flight day from Riga to Vilnius.

# Constraint for the Dublin segment: 2 days.
s.add(d1 == 2)

# Constraint for the Riga segment: 5 days.
s.add(d2 - d1 + 1 == 5)

# Constraint for the Vilnius segment: 7 days.
s.add(12 - d2 + 1 == 7)

# Enforce ordering and valid day ranges.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 12)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected outcome: d1 = 2
    d2_val = m[d2].as_long()  # Expected outcome: d2 = 6
    
    print("Trip plan found:\n")
    
    # Dublin segment.
    print("1. Stay in Dublin from Day 1 to Day {} (2 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Dublin to Riga.".format(d1_val))
    
    # Riga segment.
    print("2. Stay in Riga from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Riga to Vilnius.".format(d2_val))
    
    # Vilnius segment.
    print("3. Stay in Vilnius from Day {} to Day 12 (7 days).".format(d2_val))
else:
    print("No solution exists!")