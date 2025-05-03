from z3 import *

# In this problem, the available direct flights connect:
#   • Oslo <-> Dublin
#   • Dublin <-> Valencia
#
# Thus one valid itinerary order is:
#   Oslo -> Dublin -> Valencia
#
# We use two flight day variables:
#   d1: the day when you fly from Oslo to Dublin (the last day in Oslo, first day of Dublin)
#   d2: the day when you fly from Dublin to Valencia (the last day in Dublin, first day of Valencia)
#
# We assume the convention where:
#   • The first leg (Oslo) is from day 1 to day d1 (inclusive)
#   • The second leg (Dublin) is from day d1 to day d2 (inclusive)
#   • The third leg (Valencia) is from day d2 to day 9 (inclusive)
#
# Therefore, the duration for each city is:
#   • Oslo:         d1 days
#   • Dublin:       d2 - d1 + 1 days
#   • Valencia:     9 - d2 + 1 days i.e., (10 - d2) days
#
# The problem requirements are:
#   • Oslo for 3 days       --> d1 = 3
#   • Dublin for 3 days     --> d2 - d1 + 1 = 3
#   • Valencia for 5 days   --> 10 - d2 = 5
#
# In addition, you plan to visit relatives in Valencia between day 5 and day 9.
# In this plan, Valencia leg runs from day d2 to 9.
# With 10 - d2 = 5, we have d2 = 5, so the Valencia leg is exactly from day 5 to 9,
# ensuring that the relatives visit falls within that period.

# Set up the Z3 solver
s = Solver()

# Define the flight switching days: d1 for Oslo->Dublin, d2 for Dublin->Valencia
d1 = Int('d1')
d2 = Int('d2')

# Add duration constraints:
s.add(d1 == 3)                # Oslo leg is 3 days: days 1 to 3.
s.add(d2 - d1 + 1 == 3)         # Dublin leg is 3 days.
s.add(10 - d2 == 5)             # Valencia leg is 5 days (i.e., days 5 through 9).

# Derived values:
# From d1 == 3, the second constraint gives: d2 - 3 + 1 = 3  => d2 = 5.
# Which in turn satisfies the Valencia leg constraint.
#
# Add ordering constraints:
s.add(d1 < d2)       # Must leave Oslo for Dublin before leaving Dublin for Valencia.
s.add(d1 >= 1, d2 <= 9)

# Check for a solution:
if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()
    d2_val = model[d2].as_long()
    
    print("Trip plan found:\n")
    print("1. Stay in Oslo from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Oslo to Dublin.".format(d1_val))
    print("2. Stay in Dublin from Day {} to Day {} ({} days).".format(d1_val, d2_val, d2_val - d1_val + 1))
    print("   -> On Day {}, take a direct flight from Dublin to Valencia.".format(d2_val))
    print("3. Stay in Valencia from Day {} to Day 9 (5 days).".format(d2_val))
    print("   -> Visit relatives in Valencia between Day 5 and Day 9.")
else:
    print("No solution exists!")