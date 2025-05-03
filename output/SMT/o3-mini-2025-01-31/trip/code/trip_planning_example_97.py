from z3 import *

# We have a 14-day trip visiting 3 cities with the following requirements:
#   • Zurich: 7 days.
#   • Frankfurt: 5 days.
#   • Lyon: 4 days, with a workshop in Lyon between Day 11 and Day 14.
#
# Without overlapping, the total days would be 7 + 5 + 4 = 16 days.
# By overlapping the flight days (each flight day counts as both the last day in one city
# and the first day in the next), we can compress the itinerary into 14 days.
#
# Available direct flights:
#   • between Zurich and Frankfurt,
#   • between Frankfurt and Lyon.
#
# This fixes the itinerary order as:
#   Zurich -> Frankfurt -> Lyon.
#
# Let:
#   d1 = flight day from Zurich to Frankfurt.
#   d2 = flight day from Frankfurt to Lyon.
#
# Now define the segments:
#
# 1. Zurich segment:
#    - Runs from Day 1 to Day d1 (inclusive).
#    - Duration = d1 days.
#    - Must equal 7 days: d1 == 7.
#
# 2. Frankfurt segment:
#    - Runs from Day d1 to Day d2 (inclusive).
#    - Duration = (d2 - d1 + 1) days.
#    - Must equal 5 days: d2 - d1 + 1 == 5.
#
# 3. Lyon segment:
#    - Runs from Day d2 to Day 14 (inclusive).
#    - Duration = (14 - d2 + 1) days.
#    - Must equal 4 days: 14 - d2 + 1 == 4.
#
# Note: The entire Lyon segment (from Day 11 to Day 14 if d2 == 11) matches the workshop requirement.
#
# Let's model these constraints using the Z3 solver.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Zurich to Frankfurt.
d2 = Int('d2')  # Flight day from Frankfurt to Lyon.

# Constraint for the Zurich segment: 7 days.
s.add(d1 == 7)

# Constraint for the Frankfurt segment: 5 days.
s.add(d2 - d1 + 1 == 5)

# Constraint for the Lyon segment: 4 days.
s.add(14 - d2 + 1 == 4)

# Enforce ordering: flight from Zurich to Frankfurt happens before flight from Frankfurt to Lyon.
s.add(d1 < d2)

# Ensure flight days lie within the itinerary boundaries.
s.add(d1 >= 1, d2 <= 14)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 7
    d2_val = m[d2].as_long()  # Expected to be 11 (7 + (5 - 1) = 11)
    
    print("Trip plan found:\n")
    
    # Zurich segment.
    print("1. Stay in Zurich from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Zurich to Frankfurt.".format(d1_val))
    
    # Frankfurt segment.
    print("2. Stay in Frankfurt from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Frankfurt to Lyon.".format(d2_val))
    
    # Lyon segment.
    print("3. Stay in Lyon from Day {} to Day 14 (4 days).".format(d2_val))
    print("   -> Attend the workshop in Lyon between Day 11 and Day 14.")
else:
    print("No solution exists!")