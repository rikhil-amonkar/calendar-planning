from z3 import *

# We have a 5-day trip visiting 3 European cities.
# The requirements are:
#   • Oslo: 2 days, and you are going to attend a wedding in Oslo between Day 1 and Day 2.
#   • Vienna: 2 days.
#   • Valencia: 3 days.
#
# Note: Although the sum of the days in each city is 2 + 2 + 3 = 7 days,
# the overlap due to shared flight days lets us plan the trip in 5 days.
#
# The available direct flights are:
#   • between Oslo and Vienna,
#   • between Vienna and Valencia.
#
# We assume the following itinerary order:
#   Oslo -> Vienna -> Valencia
#
# We use the convention that when a direct flight is taken on a day,
# that day counts as both the last day in the departing city and the first day in the arriving city.
#
# Define:
#   d1 = flight day from Oslo to Vienna.
#   d2 = flight day from Vienna to Valencia.
#
# Then, the segments are:
#
# 1. Oslo segment:
#    From Day 1 to Day d1, the duration is d1 days.
#    We require Oslo for 2 days, so: d1 = 2.
#    The wedding in Oslo is attended between Day 1 and Day 2.
#
# 2. Vienna segment:
#    From Day d1 to Day d2, the duration is (d2 - d1 + 1) days.
#    We require Vienna for 2 days, so: d2 - d1 + 1 = 2.
#    With d1 = 2, this yields: d2 - 2 + 1 = 2  ->  d2 = 3.
#
# 3. Valencia segment:
#    From Day d2 to Day 5, the duration is (5 - d2 + 1) days.
#    We require Valencia for 3 days, so: 5 - d2 + 1 = 3.
#    With d2 = 3, we have: 5 - 3 + 1 = 3.
#
# The flight segments meet the overall scheduling requirements and the wedding condition.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Oslo to Vienna.
d2 = Int('d2')  # Flight day from Vienna to Valencia.

# Oslo segment: must last 2 days so d1 = 2.
s.add(d1 == 2)

# Vienna segment: must last 2 days so d2 - d1 + 1 = 2.
s.add(d2 - d1 + 1 == 2)

# Valencia segment: must last 3 days so 5 - d2 + 1 = 3.
s.add(5 - d2 + 1 == 3)

# Enforce flight sequencing and valid day boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 5)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 2 (Oslo -> Vienna flight day)
    d2_val = m[d2].as_long()  # Expected: 3 (Vienna -> Valencia flight day)
    
    print("Trip plan found:\n")
    
    # Oslo segment.
    print("1. Stay in Oslo from Day 1 to Day {} (2 days).".format(d1_val))
    print("   -> Attend the wedding in Oslo between Day 1 and Day 2.")
    print("   -> On Day {}, take a direct flight from Oslo to Vienna.".format(d1_val))
    
    # Vienna segment.
    print("2. Stay in Vienna from Day {} to Day {} (2 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Vienna to Valencia.".format(d2_val))
    
    # Valencia segment.
    print("3. Stay in Valencia from Day {} to Day 5 (3 days).".format(d2_val))
else:
    print("No solution exists!")