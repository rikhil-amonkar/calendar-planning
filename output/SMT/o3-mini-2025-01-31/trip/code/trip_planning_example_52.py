from z3 import *

# We have a 13-day trip visiting 3 European cities.
# The requirements are:
#   • Madrid: 6 days.
#   • Paris: 5 days.
#   • Reykjavik: 4 days.
#
# Additionally, you plan to visit relatives in Reykjavik between Day 10 and Day 13.
#
# The available direct flights (assuming bidirectional travel) are:
#   • Madrid and Paris,
#   • Reykjavik and Madrid,
#   • Reykjavik and Paris.
#
# To meet the requirement of meeting relatives in Reykjavik (between Day 10 and Day 13),
# we choose the itinerary ordering: Madrid -> Paris -> Reykjavik.
#
# We use the convention that when you take a flight on a day, that day counts as both the
# last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Madrid to Paris.
#   d2 = flight day from Paris to Reykjavik.
#
# Then the segments are:
#
# 1. Madrid segment:
#    From Day 1 to Day d1, the duration is d1 days.
#    We require 6 days in Madrid, so:
#      d1 = 6.
#
# 2. Paris segment:
#    From Day d1 to Day d2, the duration is (d2 - d1 + 1) days.
#    We require 5 days in Paris, so:
#      d2 - d1 + 1 = 5.
#
# 3. Reykjavik segment:
#    From Day d2 to Day 13, the duration is (13 - d2 + 1) days.
#    We require 4 days in Reykjavik, so:
#      13 - d2 + 1 = 4.
#
# Solving these equations:
#   From (1): d1 = 6.
#   From (2): d2 - 6 + 1 = 5  -->  d2 - 5 = 5  -->  d2 = 10.
#   From (3): 13 - 10 + 1 = 4  -->  4 = 4, which holds.
#
# The Reykjavik segment (Day 10 to Day 13) satisfies the relative visit requirement.
#
# Final Itinerary:
#   • Madrid from Day 1 up to Day 6 (6 days).
#       -> On Day 6, take the flight from Madrid to Paris.
#   • Paris from Day 6 up to Day 10 (5 days).
#       -> On Day 10, take the flight from Paris to Reykjavik.
#   • Reykjavik from Day 10 to Day 13 (4 days),
#       -> Visit relatives in Reykjavik between Day 10 and Day 13.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Madrid to Paris.
d2 = Int('d2')  # Flight day from Paris to Reykjavik.

# Constraint for Madrid: duration from Day 1 to d1 equals 6 days.
s.add(d1 == 6)

# Constraint for Paris: duration from d1 to d2 equals 5 days.
s.add(d2 - d1 + 1 == 5)

# Constraint for Reykjavik: duration from d2 to Day 13 equals 4 days.
s.add(13 - d2 + 1 == 4)

# Enforce the natural flight day order and valid day boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 13)

# The relatives visit in Reykjavik should occur between Day 10 and Day 13.
# Since the Reykjavik segment is from Day d2 to Day 13, we require d2 to be >= 10.
s.add(d2 >= 10)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 6 (Madrid -> Paris flight day)
    d2_val = m[d2].as_long()  # Expected to be 10 (Paris -> Reykjavik flight day)
    
    print("Trip plan found:\n")
    
    # Madrid segment.
    print("1. Stay in Madrid from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Madrid to Paris.".format(d1_val))
    
    # Paris segment.
    print("2. Stay in Paris from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Paris to Reykjavik.".format(d2_val))
    
    # Reykjavik segment.
    print("3. Stay in Reykjavik from Day {} to Day 13 (4 days).".format(d2_val))
    print("   -> Visit relatives in Reykjavik between Day 10 and Day 13.")
else:
    print("No solution exists!")