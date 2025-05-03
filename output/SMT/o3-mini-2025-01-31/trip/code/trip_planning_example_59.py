from z3 import *

# We have a 16-day trip visiting 3 European cities.
# The requirements are:
#   • Bucharest: 7 days, and you are going to attend a wedding in Bucharest which takes place between Day 1 and Day 7.
#   • Lyon: 7 days.
#   • Porto: 4 days.
#
# Note: 7 + 7 + 4 = 18 days, but we only have 16 days because flight days are shared between two consecutive segments.
# We have the following direct flight connections:
#   • Bucharest and Lyon,
#   • Lyon and Porto.
#
# We assume the itinerary order:
#   Bucharest -> Lyon -> Porto
#
# We adopt the convention that when taking a direct flight on a day,
# that day counts as both the last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Bucharest to Lyon.
#   d2 = flight day from Lyon to Porto.
#
# Then we get:
#
# 1. Bucharest segment:
#    From Day 1 to Day d1, the duration is d1 days.
#    We require 7 days in Bucharest, so: d1 = 7.
#    And the wedding in Bucharest is attended between Day 1 and Day 7.
#
# 2. Lyon segment:
#    From Day d1 to Day d2, the duration is (d2 - d1 + 1) days.
#    We require 7 days in Lyon, so: d2 - d1 + 1 = 7.
#    With d1 = 7, we have: d2 = 7 + 6 = 13.
#
# 3. Porto segment:
#    From Day d2 to Day 16, the duration is (16 - d2 + 1) days.
#    We require 4 days in Porto, so: 16 - d2 + 1 = 4.
#    With d2 = 13, we check: 16 - 13 + 1 = 4.
#
# This itinerary satisfies all the requirements.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Bucharest to Lyon.
d2 = Int('d2')  # Flight day from Lyon to Porto.

# Bucharest segment: must last 7 days, so d1 = 7.
s.add(d1 == 7)

# Lyon segment: must last 7 days, so d2 - d1 + 1 = 7.
s.add(d2 - d1 + 1 == 7)

# Porto segment: must last 4 days, so 16 - d2 + 1 = 4.
s.add(16 - d2 + 1 == 4)

# Enforce flight ordering and valid day boundaries.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 16)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 7 (Bucharest -> Lyon flight day)
    d2_val = m[d2].as_long()  # Expected to be 13 (Lyon -> Porto flight day)
    
    print("Trip plan found:\n")
    
    # Bucharest segment.
    print("1. Stay in Bucharest from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> Attend the wedding in Bucharest between Day 1 and Day 7.")
    print("   -> On Day {}, take a direct flight from Bucharest to Lyon.".format(d1_val))
    
    # Lyon segment.
    print("2. Stay in Lyon from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Lyon to Porto.".format(d2_val))
    
    # Porto segment.
    print("3. Stay in Porto from Day {} to Day 16 (4 days).".format(d2_val))
else:
    print("No solution exists!")