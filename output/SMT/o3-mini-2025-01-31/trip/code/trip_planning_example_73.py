from z3 import *

# We have a 12-day trip visiting 3 European cities with the following requirements:
#   • Helsinki: 6 days, and from day 1 to day 6 there is an annual show you want to attend in Helsinki.
#   • Venice: 4 days.
#   • Santorini: 4 days.
#
# The sum of stays if counted separately is 6 + 4 + 4 = 14 days, but by overlapping flight days the trip fits into 12 days.
#
# The available direct flights are:
#   • between Helsinki and Venice,
#   • between Venice and Santorini.
#
# We choose the itinerary order:
#   Helsinki -> Venice -> Santorini
#
# We adopt the convention that when a direct flight is taken on a day,
# that day counts as both the last day in the departing city and the first day in the arriving city.
#
# Let:
#   d1 = flight day from Helsinki to Venice.
#   d2 = flight day from Venice to Santorini.
#
# Then the trip segments become:
#
# 1. Helsinki segment:
#    Runs from Day 1 to Day d1.
#    Duration = d1 days.
#    Helsinki must be 6 days (and its annual show is between day 1 and day 6),
#    so we set d1 = 6.
#
# 2. Venice segment:
#    Runs from Day d1 to Day d2.
#    Duration = d2 - d1 + 1 days.
#    Venice must be 4 days, so we require: d2 - d1 + 1 = 4.
#    With d1 = 6, this gives: d2 - 6 + 1 = 4, so d2 = 9.
#
# 3. Santorini segment:
#    Runs from Day d2 to Day 12.
#    Duration = 12 - d2 + 1 days.
#    Santorini must be 4 days, so: 12 - d2 + 1 = 4.
#    With d2 = 9, we have: 12 - 9 + 1 = 4.
#
# This itinerary satisfies all constraints including the show in Helsinki.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Helsinki to Venice.
d2 = Int('d2')  # Flight day from Venice to Santorini.

# Helsinki segment: 6 days (and cover the annual show from day 1 to 6).
s.add(d1 == 6)

# Venice segment: 4 days.
s.add(d2 - d1 + 1 == 4)

# Santorini segment: 4 days.
s.add(12 - d2 + 1 == 4)

# Enforce flight ordering and day boundaries:
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 12)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected to be 6 (Helsinki -> Venice flight)
    d2_val = m[d2].as_long()  # Expected to be 9 (Venice -> Santorini flight)
    
    print("Trip plan found:\n")
    
    # Helsinki segment.
    print("1. Stay in Helsinki from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> Attend the annual show in Helsinki from Day 1 to Day 6.")
    print("   -> On Day {}, take a direct flight from Helsinki to Venice.".format(d1_val))
    
    # Venice segment.
    print("2. Stay in Venice from Day {} to Day {} (4 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Venice to Santorini.".format(d2_val))
    
    # Santorini segment.
    print("3. Stay in Santorini from Day {} to Day 12 (4 days).".format(d2_val))
else:
    print("No solution exists!")