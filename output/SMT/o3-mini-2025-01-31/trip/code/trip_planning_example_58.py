from z3 import *

# We have a 14-day trip visiting 3 European cities.
# The requirements are:
#   • Stockholm: 2 days.
#   • Reykjavik: 7 days, and you want to meet your friends there
#                between Day 2 and Day 8 (i.e. during the Reykjavik stay).
#   • Athens: 7 days.
#
# The available direct flights are:
#   • Stockholm and Athens,
#   • Reykjavik to Athens,
#   • Stockholm and Reykjavik.
#
# We need an itinerary with overlapping flight days.
# We decide on the following order:
#
#   Stockholm -> Reykjavik -> Athens
#
# Under the convention that when a direct flight is taken on a day,
# that day counts as the last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Stockholm to Reykjavik.
#   d2 = flight day from Reykjavik to Athens.
#
# Then:
# 1. Stockholm segment: from Day 1 to Day d1, lasting d1 days.
#    We require Stockholm for 2 days, so: d1 = 2.
#
# 2. Reykjavik segment: from Day d1 to Day d2, lasting (d2 - d1 + 1) days.
#    We require Reykjavik for 7 days, so: d2 - d1 + 1 = 7.
#    With d1 = 2, we get: d2 - 2 + 1 = 7  ->  d2 = 8.
#
# 3. Athens segment: from Day d2 to Day 14, lasting (14 - d2 + 1) days.
#    We require Athens for 7 days, so: 14 - d2 + 1 = 7.
#    With d2 = 8, we get: 14 - 8 + 1 = 7.
#
# The Reykjavik stay is from Day 2 to Day 8, which fulfills
# the requirement to meet your friends in Reykjavik between Day 2 and Day 8.
#
# Also, the flights used are:
#   - From Stockholm to Reykjavik (available as "Stockholm and Reykjavik").
#   - From Reykjavik to Athens (available as "from Reykjavik to Athens").
#
# This itinerary meets all requirements.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Stockholm to Reykjavik.
d2 = Int('d2')  # Flight day from Reykjavik to Athens.

# Stockholm segment: must last 2 days
s.add(d1 == 2)

# Reykjavik segment: must last 7 days => d2 - d1 + 1 == 7
s.add(d2 - d1 + 1 == 7)

# Athens segment: must last 7 days => 14 - d2 + 1 == 7
s.add(14 - d2 + 1 == 7)

# Enforce flight order and valid boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 14)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 2 (flight from Stockholm to Reykjavik)
    d2_val = m[d2].as_long()  # Expected: 8 (flight from Reykjavik to Athens)
    
    print("Trip plan found:\n")
    
    # Stockholm segment.
    print("1. Stay in Stockholm from Day 1 to Day {} (2 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Stockholm to Reykjavik.".format(d1_val))
    
    # Reykjavik segment.
    print("2. Stay in Reykjavik from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> Meet your friends in Reykjavik between Day 2 and Day 8.")
    print("   -> On Day {}, take a direct flight from Reykjavik to Athens.".format(d2_val))
    
    # Athens segment.
    print("3. Stay in Athens from Day {} to Day 14 (7 days).".format(d2_val))
else:
    print("No solution exists!")