from z3 import *

# Define integer variables:
# d1: flight day from Porto to Oslo (overlap day for Porto and Oslo)
# d2: flight day from Oslo to Dubrovnik (overlap day for Oslo and Dubrovnik)
d1 = Int('d1')
d2 = Int('d2')

s = Solver()

# The overall trip is from day 1 to day 16.
# We assume the itinerary follows the order given by available flights:
#   Porto -> Oslo -> Dubrovnik.
#
# If we use the convention that the first city is visited from day 1 up to day d1 (inclusive),
# the second from day d1 to day d2 (inclusive), and the third from day d2 to day 16 (inclusive),
# then the duration in each city is:
#
#   Porto:      d1 days   (must equal 7)
#   Oslo:       d2 - d1 + 1 days   (must equal 6)
#   Dubrovnik:  16 - d2 + 1 days   (must equal 5)
#
# Additionally, you must attend a conference in Dubrovnik on day 12 and day 16.
# For that to happen, Dubrovnik must be visited on both day 12 and day 16,
# i.e. day 12 (and obviously day 16) must be within the Dubrovnik leg, which starts on day d2.
#
# Here are the constraints:

# Duration constraints:
s.add(d1 == 7)               # Porto must be visited for 7 days: days 1...d1 = 7 days.
s.add(d2 - d1 + 1 == 6)        # Oslo is visited for 6 days.
s.add(16 - d2 + 1 == 5)        # Dubrovnik is visited for 5 days.

# These equations force:
#   d1 = 7
#   d2 = d1 + 5 = 12 
#   And Dubrovnik duration becomes: 16 - 12 + 1 = 5 days.

# Chronological ordering:
s.add(d1 >= 1, d2 > d1, d2 <= 16)

# Conference constraints: 
# You must be in Dubrovnik (i.e. in the leg starting on day d2) on day 12 and day 16.
# For day 12 to be during the Dubrovnik leg, we require:
s.add(d2 <= 12)   # then day 12 ∈ [d2, 16]
# Day 16 is the final day of the trip, so it is automatically in Dubrovnik.

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()
    d2_val = model[d2].as_long()
    
    print("Trip plan found:\n")
    print("  1. Stay in Porto: Days 1 to", d1_val, "(7 days)")
    print("  2. Flight from Porto to Oslo on day:", d1_val)
    print("     Stay in Oslo: Days", d1_val, "to", d2_val, "(6 days, with day", d1_val, "as flight overlap)")
    print("  3. Flight from Oslo to Dubrovnik on day:", d2_val)
    print("     Stay in Dubrovnik: Days", d2_val, "to 16 (5 days, with day", d2_val, "as flight overlap)")
    print("  4. Conference in Dubrovnik on day 12 and day 16")
else:
    print("No solution exists!")