from z3 import *

# We have a 10-day trip visiting 3 European cities.
# The requirements are:
#   • Lyon: 3 days.
#   • Frankfurt: 2 days.
#   • Vilnius: 7 days.
#
# Additionally, you must attend a wedding in Vilnius between Day 4 and Day 10.
#
# The available direct flights are:
#   • between Lyon and Frankfurt,
#   • between Frankfurt and Vilnius.
#
# We assume the itinerary order is:
#   Lyon -> Frankfurt -> Vilnius.
#
# We use the convention that when you take a direct flight on a day,
# that day counts as the last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Lyon to Frankfurt.
#   d2 = flight day from Frankfurt to Vilnius.
#
# Then the segments are:
#
# 1. Lyon: Days 1 to d1, duration = d1 days.
#    We need a 3-day stay, so: d1 = 3.
#
# 2. Frankfurt: Days d1 to d2, duration = d2 - d1 + 1.
#    We need a 2-day stay, so: d2 - d1 + 1 = 2, which implies d2 = d1 + 1.
#    With d1 = 3, we get d2 = 4.
#
# 3. Vilnius: Days d2 to Day 10, duration = 10 - d2 + 1.
#    We need a 7-day stay, so: 10 - d2 + 1 = 7, which implies 11 - d2 = 7, so d2 = 4.
#
# The wedding in Vilnius must take place between Day 4 and Day 10.
# Since the Vilnius segment spans Day 4 to Day 10, the wedding requirement is satisfied.
#
# The final plan is:
#   • Stay in Lyon from Day 1 to Day 3 (3 days).
#       -> On Day 3, take a direct flight from Lyon to Frankfurt.
#   • Stay in Frankfurt from Day 3 to Day 4 (2 days).
#       -> On Day 4, take a direct flight from Frankfurt to Vilnius.
#   • Stay in Vilnius from Day 4 to Day 10 (7 days).
#       -> Attend the wedding in Vilnius between Day 4 and Day 10.
#
# Note: The overlapping days occur due to the flight day counting for both cities.

s = Solver()

# Define flight day variables.
d1 = Int('d1')  # Flight day from Lyon to Frankfurt.
d2 = Int('d2')  # Flight day from Frankfurt to Vilnius.

# Constraint for Lyon segment (3 days): from Day 1 to d1.
s.add(d1 == 3)

# Constraint for Frankfurt segment (2 days): duration = d2 - d1 + 1.
s.add(d2 - d1 + 1 == 2)

# Constraint for Vilnius segment (7 days): duration = 10 - d2 + 1.
s.add(10 - d2 + 1 == 7)

# Enforce flight order and valid day boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 10)

# The wedding in Vilnius must occur between Day 4 and Day 10.
# Since Vilnius is visited from Day d2 (which is 4) to Day 10, this requirement is inherently satisfied,
# but we can add a constraint that ensures the start of the Vilnius segment is no earlier than Day 4.
s.add(d2 >= 4)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 3 (flight from Lyon to Frankfurt)
    d2_val = m[d2].as_long()  # Expected: 4 (flight from Frankfurt to Vilnius)
    
    print("Trip plan found:\n")
    
    # Lyon segment.
    print("1. Stay in Lyon from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Lyon to Frankfurt.".format(d1_val))
    
    # Frankfurt segment.
    print("2. Stay in Frankfurt from Day {} to Day {} (2 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Frankfurt to Vilnius.".format(d2_val))
    
    # Vilnius segment.
    print("3. Stay in Vilnius from Day {} to Day 10 (7 days).".format(d2_val))
    print("   -> Attend the wedding in Vilnius between Day 4 and Day 10.")
else:
    print("No solution exists!")