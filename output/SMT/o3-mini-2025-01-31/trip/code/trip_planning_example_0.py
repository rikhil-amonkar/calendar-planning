from z3 import *

# Define integer variables:
# d1: flight day from Helsinki to Barcelona (overlap day: counts for both)
# d2: flight day from Barcelona to Florence (overlap day: counts for both)
# m: day when you meet your friend in Florence
d1 = Int('d1')
d2 = Int('d2')
m  = Int('m')

s = Solver()

# Basic domain assumptions:
# The trip overall is days 1 through 14.
s.add(d1 >= 1, d1 < d2, d2 <= 14)

# The "visit counts" are modeled as follows.
# Helsinki is visited on days 1 through d1. (Count = d1 days)
# Barcelona is visited on days d1 through d2. (Count = d2 - d1 + 1 days, since d1 is overlapping)
# Florence is visited on days d2 through 14. (Count = 14 - d2 + 1 days, since d2 is overlapping)

# We require exactly 5 days in Helsinki, 5 in Barcelona, and 6 in Florence.
s.add(d1 == 5)
s.add(d2 - d1 + 1 == 5)
s.add(14 - d2 + 1 == 6)

# Friend meeting must occur in Florence between day 9 and day 14.
# Moreover, as Florence is visited starting on day d2, we require m to be in the Florence block.
s.add(m >= 9, m <= 14)
s.add(m >= d2)

# Flight connectivity constraints:
# The only direct flights you take are:
#    • From Helsinki to Barcelona, and
#    • From Barcelona to Florence.
# (Given the problem statement, we do not need extra Boolean variables for flight existences.)

# Check for satisfiability and print the solution.
if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()
    d2_val = model[d2].as_long()
    m_val  = model[m].as_long()
    
    print("Trip plan found:\n")
    print(" Flight from Helsinki to Barcelona on day:", d1_val)
    print(" Flight from Barcelona to Florence on day:", d2_val)
    print(" Meet your friend in Florence on day:", m_val)
    print("\nItinerary breakdown:")
    print(" Helsinki: Days 1 to", d1_val, " (5 days)")
    print(" Barcelona: Days", d1_val, "to", d2_val, " (5 days; note day", d1_val, "overlaps with Helsinki)")
    print(" Florence: Days", d2_val, "to 14 (6 days; note day", d2_val, "overlaps with Barcelona)")
else:
    print("No solution exists!")