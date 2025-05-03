from z3 import *

# We have a 12-day trip visiting 3 European cities with the following requirements:
#   • Geneva: 6 days.
#   • Brussels: 6 days.
#   • Riga: 2 days, with a visit to relatives in Riga between Day 11 and Day 12.
#
# Although the sum of days is 6 + 6 + 2 = 14 days,
# by overlapping on the flight days (each flight day counts as the last day at the departing city
# and the first day at the arriving city), the trip fits into 12 days.
#
# The available direct flights are:
#   • between Geneva and Brussels,
#   • between Brussels and Riga.
#
# We choose the itinerary order:
#   Geneva -> Brussels -> Riga
#
# We adopt the convention that when a direct flight is taken on a day,
# that day is used as both the final day at the departing city and the first day at the arriving city.
#
# Let:
#   d1 = flight day from Geneva to Brussels.
#   d2 = flight day from Brussels to Riga.
#
# Then the segments are defined as follows:
#
# 1. Geneva segment:
#    Runs from Day 1 to Day d1.
#    Duration = d1 days.
#    Requirement: 6 days in Geneva, so d1 must equal 6.
#
# 2. Brussels segment:
#    Runs from Day d1 to Day d2.
#    Duration = d2 - d1 + 1 days.
#    Requirement: 6 days in Brussels, so d2 - d1 + 1 = 6.
#    With d1 = 6, this implies d2 = 11.
#
# 3. Riga segment:
#    Runs from Day d2 to Day 12.
#    Duration = 12 - d2 + 1 days.
#    Requirement: 2 days in Riga, so 12 - d2 + 1 = 2.
#    With d2 = 11, we get: 12 - 11 + 1 = 2.
#
# The requirement to visit relatives in Riga between Day 11 and Day 12 is met by the Riga segment.
#
# This itinerary satisfies all the constraints.
s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Geneva to Brussels.
d2 = Int('d2')  # Flight day from Brussels to Riga.

# Geneva segment: must last 6 days.
s.add(d1 == 6)

# Brussels segment: must last 6 days, i.e., d2 - d1 + 1 = 6.
s.add(d2 - d1 + 1 == 6)

# Riga segment: must last 2 days, i.e., 12 - d2 + 1 = 2.
s.add(12 - d2 + 1 == 2)

# Enforce flight ordering and valid day boundaries:
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 12)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 6 (Geneva -> Brussels flight)
    d2_val = m[d2].as_long()  # Expected to be 11 (Brussels -> Riga flight)
    
    print("Trip plan found:\n")
    
    # Geneva segment.
    print("1. Stay in Geneva from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Geneva to Brussels.".format(d1_val))
    
    # Brussels segment.
    print("2. Stay in Brussels from Day {} to Day {} (6 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Brussels to Riga.".format(d2_val))
    
    # Riga segment.
    print("3. Stay in Riga from Day {} to Day 12 (2 days).".format(d2_val))
    print("   -> Visit your relatives in Riga between Day 11 and Day 12.")
else:
    print("No solution exists!")