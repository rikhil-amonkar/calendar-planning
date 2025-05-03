from z3 import *

# Define integer variables:
# d1: flight day from Berlin to Warsaw (overlap day for Berlin and Warsaw)
# d2: flight day from Warsaw to Bucharest (overlap day for Warsaw and Bucharest)
# m: day to meet your friend in Bucharest
d1 = Int('d1')
d2 = Int('d2')
m  = Int('m')

s = Solver()

# Overall trip is from day 1 to day 6.
# We assume the itinerary order: Berlin -> Warsaw -> Bucharest.
# The visits are thus:
#   Berlin: Days 1 to d1         (duration = d1 - 1 + 1 = d1 days)
#   Warsaw: Days d1 to d2        (duration = d2 - d1 + 1 days)
#   Bucharest: Days d2 to 6        (duration = 6 - d2 + 1 days)
#
# Requirements:
#   - Berlin: 3 days  => d1 = 3
#   - Warsaw: 3 days  => d2 - d1 + 1 = 3  => d2 = d1 + 2 = 5 (since d1=3)
#   - Bucharest: 2 days  => 6 - d2 + 1 = 2 => d2 = 5
#
# Friend meeting in Bucharest must occur between day 5 and day 6,
# and since Bucharest is visited from day d2 (which equals 5) to day 6,
# we must have m in {5, 6} with m >= d2.
s.add(d1 == 3)
s.add(d2 - d1 + 1 == 3)
s.add(6 - d2 + 1 == 2)

# Ensure the flight order and day range constraints.
s.add(d1 < d2, d2 <= 6, d1 >= 1)

# Friend meeting in Bucharest between day 5 and day 6 (and after arrival)
s.add(m >= 5, m <= 6, m >= d2)

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()
    d2_val = model[d2].as_long()
    m_val  = model[m].as_long()
    
    print("Trip plan found:\n")
    print(" Flight from Berlin to Warsaw on day:", d1_val)
    print(" Flight from Warsaw to Bucharest on day:", d2_val)
    print(" Meet your friend in Bucharest on day:", m_val)
    print("\nItinerary breakdown:")
    print(" Berlin: Days 1 to", d1_val, "(3 days)")
    print(" Warsaw: Days", d1_val, "to", d2_val, "(3 days; note day", d1_val, "overlaps with Berlin)")
    print(" Bucharest: Days", d2_val, "to 6 (2 days; note day", d2_val, "overlaps with Warsaw)")
else:
    print("No solution exists!")