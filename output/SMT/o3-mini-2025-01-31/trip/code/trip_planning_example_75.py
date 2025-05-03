from z3 import *

# We have a 17-day trip visiting 3 European cities with the following requirements:
#   • Valencia: 7 days, and from Day 11 to Day 17 there is an annual show in Valencia.
#   • Prague: 7 days.
#   • Tallinn: 5 days.
#
# Although the durations add up to 7 + 7 + 5 = 19 days, overlapping flight days allow us to fit the trip into 17 days.
#
# The available direct flights are:
#   • between Prague and Valencia,
#   • between Tallinn and Prague.
#
# We choose the itinerary order:
#   Tallinn -> Prague -> Valencia
#
# We adopt the convention that when a direct flight is taken on a day,
# that day counts as the last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Tallinn to Prague.
#   d2 = flight day from Prague to Valencia.
#
# Then the trip segments are defined as:
#
# 1. Tallinn segment:
#    Runs from Day 1 to Day d1.
#    Duration = d1 days.
#    Requirement: 5 days in Tallinn, so we set d1 = 5.
#
# 2. Prague segment:
#    Runs from Day d1 to Day d2.
#    Duration = d2 - d1 + 1 days.
#    Requirement: 7 days in Prague, hence: d2 - d1 + 1 = 7.
#                        With d1 = 5, we get d2 = 11.
#
# 3. Valencia segment:
#    Runs from Day d2 to Day 17.
#    Duration = 17 - d2 + 1 days.
#    Requirement: 7 days in Valencia, hence: 17 - d2 + 1 = 7.
#                        With d2 = 11, we get 17 - 11 + 1 = 7.
#
# This itinerary ensures that the Valencia segment is from Day 11 to Day 17, covering the annual show.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Tallinn to Prague.
d2 = Int('d2')  # Flight day from Prague to Valencia.

# Tallinn segment: must last 5 days.
s.add(d1 == 5)

# Prague segment: must last 7 days.
s.add(d2 - d1 + 1 == 7)

# Valencia segment: must last 7 days.
s.add(17 - d2 + 1 == 7)

# Ensure flight ordering and valid day boundaries:
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 17)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected 5 (flight from Tallinn to Prague)
    d2_val = m[d2].as_long()  # Expected 11 (flight from Prague to Valencia)
    
    print("Trip plan found:\n")
    
    # Tallinn segment.
    print("1. Stay in Tallinn from Day 1 to Day {} (5 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Tallinn to Prague.".format(d1_val))
    
    # Prague segment.
    print("2. Stay in Prague from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Prague to Valencia.".format(d2_val))
    
    # Valencia segment.
    print("3. Stay in Valencia from Day {} to Day 17 (7 days).".format(d2_val))
    print("   -> Attend the annual show in Valencia from Day 11 to Day 17.")
else:
    print("No solution exists!")