from z3 import *

# We have an 11-day trip visiting 3 European cities.
# The requirements are:
#   • Krakow: 5 days, and an annual show you want to attend in Krakow runs from Day 1 to Day 5.
#   • Frankfurt: 2 days.
#   • Salzburg: 6 days.
#
# The available direct flights are:
#   • between Krakow and Frankfurt,
#   • between Frankfurt and Salzburg.
#
# We assume the itinerary order is:
#   Krakow -> Frankfurt -> Salzburg.
#
# Using the convention that when you take a direct flight on a day,
# that day counts as both the last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Krakow to Frankfurt.
#   d2 = flight day from Frankfurt to Salzburg.
#
# Then the segments are as follows:
#
# 1. Krakow segment:
#    From Day 1 to Day d1, the duration is d1 days.
#    We require 5 days in Krakow, so we have: d1 = 5.
#    Also, the annual show in Krakow runs from Day 1 to Day 5,
#    which fits exactly with the Krakow segment.
#
# 2. Frankfurt segment:
#    From Day d1 to Day d2, the duration is (d2 - d1 + 1) days.
#    We require 2 days in Frankfurt, so: d2 - d1 + 1 = 2.
#    With d1 = 5, this gives: d2 - 5 + 1 = 2  ->  d2 = 6.
#
# 3. Salzburg segment:
#    From Day d2 to Day 11, the duration is (11 - d2 + 1) days.
#    We require 6 days in Salzburg, so: 11 - d2 + 1 = 6.
#    With d2 = 6, we have: 11 - 6 + 1 = 6, which is satisfied.
#
# Final Itinerary:
#   • Stay in Krakow from Day 1 to Day 5 (5 days), and attend the annual show.
#         -> On Day 5, take a direct flight from Krakow to Frankfurt.
#   • Stay in Frankfurt from Day 5 to Day 6 (2 days).
#         -> On Day 6, take a direct flight from Frankfurt to Salzburg.
#   • Stay in Salzburg from Day 6 to Day 11 (6 days).

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Krakow to Frankfurt.
d2 = Int('d2')  # Flight day from Frankfurt to Salzburg.

# Constraint for Krakow: duration = d1 must equal 5 days (and therefore the show is attended from Day 1 to 5)
s.add(d1 == 5)

# Constraint for Frankfurt: duration = d2 - d1 + 1 must equal 2 days.
s.add(d2 - d1 + 1 == 2)

# Constraint for Salzburg: duration = 11 - d2 + 1 must equal 6 days.
s.add(11 - d2 + 1 == 6)

# Enforce valid flight order and boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 11)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # expected to be 5 (Krakow -> Frankfurt)
    d2_val = m[d2].as_long()  # expected to be 6 (Frankfurt -> Salzburg)
    
    print("Trip plan found:\n")
    
    # Krakow segment.
    print("1. Stay in Krakow from Day 1 to Day {} (5 days).".format(d1_val))
    print("   -> Attend the annual show in Krakow from Day 1 to Day 5.")
    print("   -> On Day {}, take a direct flight from Krakow to Frankfurt.".format(d1_val))
    
    # Frankfurt segment.
    print("2. Stay in Frankfurt from Day {} to Day {} (2 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Frankfurt to Salzburg.".format(d2_val))
    
    # Salzburg segment.
    print("3. Stay in Salzburg from Day {} to Day 11 (6 days).".format(d2_val))
else:
    print("No solution exists!")