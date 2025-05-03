from z3 import *

# Define integer variables:
# d1: flight day from Riga to Manchester (overlapping day for Riga and Manchester)
# d2: flight day from Manchester to Split (overlapping day for Manchester and Split)
d1 = Int('d1')
d2 = Int('d2')

s = Solver()

# The trip overall covers days 1 to 15:
#   Riga is visited from day 1 to d1 (counting d1).
#   Manchester is visited from day d1 to d2 (counting both ends).
#   Split is visited from day d2 to 15 (counting d2).
#
# We require 7 days in Riga, 4 days in Manchester, and 6 days in Split.
# This gives:
#   Riga: d1 must be 7 (days 1 ... 7)
#   Manchester: d2 - d1 + 1 = 4  =>  d2 = d1 + 3
#   Split: 15 - d2 + 1 = 6  => 16 - d2 = 6  =>  d2 = 10

s.add(d1 == 7)            # Riga days = 7
s.add(d2 - d1 + 1 == 4)     # Manchester days = 4
s.add(16 - d2 == 6)         # Split days = 6
s.add(d1 < d2, d2 <= 15, d1 >= 1)

# The direct flight connectivity in the problem is:
#   • Riga and Manchester (flight from Riga to Manchester allowed),
#   • Manchester to Split.
# These match the chosen flight days.

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()
    d2_val = model[d2].as_long()
    
    print("Trip plan found:\n")
    print(" Flight from Riga to Manchester on day:", d1_val)
    print(" Flight from Manchester to Split on day:", d2_val)
    print("\nItinerary breakdown:")
    print(" Riga: Days 1 to", d1_val, "(7 days)")
    print(" Manchester: Days", d1_val, "to", d2_val, "(4 days; note day", d1_val, "overlaps with Riga)")
    print(" Split: Days", d2_val, "to 15 (6 days; note day", d2_val, "overlaps with Manchester)")
else:
    print("No solution exists!")