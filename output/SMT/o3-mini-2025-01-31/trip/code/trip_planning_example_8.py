from z3 import *

# We use two flight day variables:
# d1: flight day from Athens to Zurich (the last day of the Athens leg)
# d2: flight day from Zurich to Krakow (the last day of the Zurich leg)
#
# We plan the itinerary in the following order:
#   Athens -> Zurich -> Krakow
#
# Using our convention:
#   - Athens is visited from day 1 to d1 (inclusive)
#   - Zurich is visited from day d1 to d2 (inclusive)
#   - Krakow is visited from day d2 to day 16 (inclusive)
#
# The problem requirements:
#   * Athens for 7 days  ->  d1 = 7
#   * Zurich for 5 days   ->  d2 - d1 + 1 = 5
#   * Krakow for 6 days   -> 16 - d2 + 1 = 6
#
# The extra condition is that you plan to visit relatives in Athens 
# between day 1 and day 7. Since the Athens leg covers exactly days 1 to 7 (when d1 = 7),
# this condition is naturally met.
#
# Additionally, the available direct flights are:
#   - Between Athens and Zurich
#   - Between Zurich and Krakow
#
# This supports our chosen itinerary order.

# Create the solver
s = Solver()

# Duration constraints:
s.add(d1 == 7)                        # Athens must be 7 days: Day 1 to day 7.
s.add(d2 - d1 + 1 == 5)                 # Zurich must be 5 days.
s.add(16 - d2 + 1 == 6)                 # Krakow must be 6 days.

# The above gives:
#   d1 = 7
#   d2 - 7 + 1 = 5  --> d2 = 7 + 4 = 11
#   And 16 - d2 + 1 = 17 - d2 = 6  --> d2 = 11, which is consistent.

# Ordering and timeline constraints:
s.add(d1 < d2)           # Must take flight from Athens to Zurich before flying to Krakow.
s.add(d1 >= 1, d2 <= 16)

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()
    d2_val = model[d2].as_long()
    
    print("Trip plan found:\n")
    print("  1. Stay in Athens from Day 1 to Day", d1_val, "(7 days)")
    print("     [Visit relatives in Athens between Day 1 and Day 7]")
    print("  2. On Day", d1_val, "take a direct flight from Athens to Zurich.")
    print("     Stay in Zurich from Day", d1_val, "to Day", d2_val, "(5 days)")
    print("  3. On Day", d2_val, "take a direct flight from Zurich to Krakow.")
    print("     Stay in Krakow from Day", d2_val, "to Day 16", "(6 days)")
else:
    print("No solution exists!")