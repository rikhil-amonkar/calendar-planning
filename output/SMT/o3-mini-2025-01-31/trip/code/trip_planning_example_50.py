from z3 import *

# We have a 12-day trip visiting 3 European cities.
# The requirements are:
#   • Vilnius: 4 days.
#   • Munich: 3 days.
#   • Mykonos: 7 days.
#
# The available direct flights are:
#   • from Vilnius to Munich,
#   • between Munich and Mykonos.
#
# We adopt the itinerary order: Vilnius -> Munich -> Mykonos.
# We use the convention that when you take a flight on a day, that day counts as both the last day
# at the departing city and the first day at the arriving city.
#
# Let:
#   d1 = flight day from Vilnius to Munich.
#   d2 = flight day from Munich to Mykonos.
#
# Then we define the segments as:
#
# 1. Vilnius: Days 1 to d1, duration = d1.
#    Required: 4 days, so: d1 = 4.
#
# 2. Munich: Days d1 to d2, duration = d2 - d1 + 1.
#    Required: 3 days, so: d2 - d1 + 1 = 3.
#    With d1 = 4, we get: d2 - 4 + 1 = 3  -> d2 - 3 = 3  -> d2 = 6.
#
# 3. Mykonos: Days d2 to 12, duration = 12 - d2 + 1.
#    Required: 7 days, so: 12 - d2 + 1 = 7  -> 13 - d2 = 7  -> d2 = 6.
#
# This results in:
#   d1 = 4 and d2 = 6.
#
# Thus, the trip plan is:
#   • Stay in Vilnius from Day 1 to Day 4 (4 days).
#       -> On Day 4, take a flight from Vilnius to Munich.
#   • Stay in Munich from Day 4 to Day 6 (3 days).
#       -> On Day 6, take a flight from Munich to Mykonos.
#   • Stay in Mykonos from Day 6 to Day 12 (7 days).

s = Solver()

# Define the flight day variables.
d1 = Int('d1')  # Flight day from Vilnius to Munich.
d2 = Int('d2')  # Flight day from Munich to Mykonos.

# Add constraints for each city segment:

# Vilnius segment: Days 1 to d1 should be 4 days.
s.add(d1 == 4)

# Munich segment: Days d1 to d2 should last 3 days.
s.add(d2 - d1 + 1 == 3)

# Mykonos segment: Days d2 to 12 should last 7 days.
s.add(12 - d2 + 1 == 7)

# Enforce flight order and valid day constraints.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 12)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 4
    d2_val = m[d2].as_long()  # Expected: 6
    
    print("Trip plan found:\n")
    
    # Vilnius segment
    print("1. Stay in Vilnius from Day 1 to Day {} (4 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Vilnius to Munich.".format(d1_val))
    
    # Munich segment
    print("2. Stay in Munich from Day {} to Day {} (3 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Munich to Mykonos.".format(d2_val))
    
    # Mykonos segment
    print("3. Stay in Mykonos from Day {} to Day 12 (7 days).".format(d2_val))
else:
    print("No solution exists!")