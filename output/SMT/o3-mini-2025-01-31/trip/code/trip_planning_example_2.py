from z3 import *

# Define integer variables:
# d1: flight day from Reykjavik to Vienna (overlapping day for Reykjavik and Vienna)
# d2: flight day from Vienna to Venice (overlapping day for Vienna and Venice)
# m: day of the wedding in Venice
d1 = Int('d1')
d2 = Int('d2')
m  = Int('m')

s = Solver()

# The trip overall is from day 1 to day 11.
# We assume the following itinerary sequence:
#   Reykjavik: Days 1 to d1 (inclusive)
#   Vienna: Days d1 to d2 (inclusive)
#   Venice: Days d2 to 11 (inclusive)
#
# The days in each city are:
#   Reykjavik: d1 days.
#   Vienna: d2 - d1 + 1 days.
#   Venice: 11 - d2 + 1 days.
#
# We require:
#   - 2 days in Reykjavik.
#   - 7 days in Vienna.
#   - 4 days in Venice.
#
# Additionally, the wedding in Venice is attended on a day m with 8 <= m <= 11,
# and since Venice is visited beginning on day d2, we require m >= d2.

s.add(d1 == 2)                            # Reykjavik: days 1 to 2 = 2 days.
s.add(d2 - d1 + 1 == 7)                     # Vienna: days d1 to d2 = 7 days.
s.add(11 - d2 + 1 == 4)                     # Venice: days d2 to 11 = 4 days.

# Combine flight day constraints with overall trip timeline
s.add(d1 < d2, d2 <= 11, d1 >= 1)

# Wedding constraints: must be in Venice between day 8 and 11,
# and since Venice is visited from day d2, it must be that m >= d2.
s.add(m >= 8, m <= 11, m >= d2)

# Check for a solution
if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()
    d2_val = model[d2].as_long()
    m_val  = model[m].as_long()
    
    print("Trip plan found:\n")
    print(" Flight from Reykjavik to Vienna on day:", d1_val)
    print(" Flight from Vienna to Venice on day:", d2_val)
    print(" Attend the wedding in Venice on day:", m_val)
    print("\nItinerary breakdown:")
    print(" Reykjavik: Days 1 to", d1_val, " (2 days)")
    print(" Vienna: Days", d1_val, "to", d2_val, " (7 days; note day", d1_val, "overlaps)")
    print(" Venice: Days", d2_val, "to 11 (4 days; note day", d2_val, "overlaps)")
else:
    print("No solution exists!")