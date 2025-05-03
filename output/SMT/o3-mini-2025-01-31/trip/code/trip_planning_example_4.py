from z3 import *

# Define integer variables:
# d1: flight day from Seville to Munich (overlap day for Seville and Munich)
# d2: flight day from Munich to Tallinn (overlap day for Munich and Tallinn)
# m: day to meet your friend in Tallinn
d1 = Int('d1')
d2 = Int('d2')
m  = Int('m')

s = Solver()

# The overall trip is from day 1 to day 12.
# We assume the itinerary order must follow the available direct flights:
#   Seville -> Munich -> Tallinn.
#
# That gives us:
#   Seville: Days 1 to d1         (duration = d1 days)
#   Munich: Days d1 to d2         (duration = d2 - d1 + 1 days)
#   Tallinn: Days d2 to 12        (duration = 12 - d2 + 1 days)
#
# Requirements:
#   Seville: 7 days  => d1 must equal 7.
#   Munich: 5 days   => d2 - d1 + 1 = 5 -> d2 = d1 + 4.
#   Tallinn: 2 days  => 12 - d2 + 1 = 2 -> 13 - d2 = 2 -> d2 = 11.
#
# Additionally, the friend meeting in Tallinn must happen between day 11 and day 12,
# and since Tallinn is visited from day d2 to day 12, we require m >= d2.
s.add(d1 == 7)
s.add(d2 - d1 + 1 == 5)
s.add(13 - d2 == 2)

# Flight order and overall timeline constraints.
s.add(d1 < d2, d2 <= 12, d1 >= 1)

# Friend meeting in Tallinn should occur between day 11 and 12 (and after arrival)
s.add(m >= 11, m <= 12, m >= d2)

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()
    d2_val = model[d2].as_long()
    m_val  = model[m].as_long()
    
    print("Trip plan found:\n")
    print(" Flight from Seville to Munich on day:", d1_val)
    print(" Flight from Munich to Tallinn on day:", d2_val)
    print(" Meet your friend in Tallinn on day:", m_val)
    print("\nItinerary breakdown:")
    print(" Seville: Days 1 to", d1_val, "(7 days)")
    print(" Munich: Days", d1_val, "to", d2_val, "(5 days; note day", d1_val, "overlaps with Seville)")
    print(" Tallinn: Days", d2_val, "to 12 (2 days; note day", d2_val, "overlaps with Munich)")
else:
    print("No solution exists!")