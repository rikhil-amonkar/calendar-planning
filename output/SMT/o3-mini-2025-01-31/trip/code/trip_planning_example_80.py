from z3 import *

# We have a 14-day trip visiting 3 cities with the following requirements:
#   • Valencia: 5 days.
#   • Copenhagen: 4 days.
#   • Riga: 7 days, with a requirement to visit relatives in Riga between Day 8 and Day 14.
#
# The total individual durations sum to 5 + 4 + 7 = 16 days, but by overlapping the flight days 
# (each flight day counts as both the last day in one city and the first day in the next), we can fit 
# the trip into 14 days.
#
# Available direct flights:
#   • between Valencia and Copenhagen,
#   • between Copenhagen and Riga.
#
# We choose the itinerary order:
#   Valencia -> Copenhagen -> Riga
#
# Using the convention that a direct flight taken on a day counts as both the last day in the departing
# city and the first day in the arriving city, we set:
#
# Let:
#   d1 = flight day from Valencia to Copenhagen.
#   d2 = flight day from Copenhagen to Riga.
#
# Then the segments become:
#
# 1. Valencia segment:
#    - Starts at Day 1 and ends at Day d1.
#    - Duration = d1 days.
#    - Must be 5 days, hence: d1 = 5.
#
# 2. Copenhagen segment:
#    - Starts at Day d1 and ends at Day d2.
#    - Duration = d2 - d1 + 1 days.
#    - Must be 4 days, hence: d2 - d1 + 1 = 4.
#      With d1 = 5, we calculate: d2 - 5 + 1 = 4  =>  d2 = 8.
#
# 3. Riga segment:
#    - Starts at Day d2 and ends at Day 14.
#    - Duration = 14 - d2 + 1 days.
#    - Must be 7 days, hence: 14 - d2 + 1 = 7.
#      With d2 = 8, we have 14 - 8 + 1 = 7.
#
# The Riga segment then spans Days 8 to 14, which fulfills the requirement to visit relatives between Day 8 and Day 14.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Valencia to Copenhagen.
d2 = Int('d2')  # Flight day from Copenhagen to Riga.

# Valencia segment: must last 5 days.
s.add(d1 == 5)

# Copenhagen segment: must last 4 days.
s.add(d2 - d1 + 1 == 4)

# Riga segment: must last 7 days.
s.add(14 - d2 + 1 == 7)

# Additional ordering and valid day constraints:
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 14)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected flight day: 5 (Valencia -> Copenhagen)
    d2_val = m[d2].as_long()  # Expected flight day: 8 (Copenhagen -> Riga)
    
    print("Trip plan found:\n")
    
    # Valencia segment.
    print("1. Stay in Valencia from Day 1 to Day {} (5 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Valencia to Copenhagen.".format(d1_val))
    
    # Copenhagen segment.
    print("2. Stay in Copenhagen from Day {} to Day {} (4 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Copenhagen to Riga.".format(d2_val))
    
    # Riga segment.
    print("3. Stay in Riga from Day {} to Day 14 (7 days).".format(d2_val))
    print("   -> Visit your relatives in Riga between Day 8 and Day 14.")
else:
    print("No solution exists!")