from z3 import *

# We have a 10-day trip visiting 3 cities with the following requirements:
#   • Helsinki: 4 days, during which from Day 1 to Day 4 there is an annual show to attend.
#   • Warsaw: 4 days.
#   • Bucharest: 4 days.
#
# The sum of individual durations is 4 + 4 + 4 = 12 days.
# By overlapping the flight days (each flight day counts as both the last day in the departing city
# and the first day in the arriving city), we can arrange the trip in 10 days.
#
# Available direct flights:
#   • between Helsinki and Warsaw,
#   • between Warsaw and Bucharest.
#
# We choose the itinerary order:
#   Helsinki -> Warsaw -> Bucharest
#
# Define:
#   d1 = flight day from Helsinki to Warsaw.
#   d2 = flight day from Warsaw to Bucharest.
#
# Then the segments become:
#
# 1. Helsinki segment:
#    - Runs from Day 1 to Day d1.
#    - Duration = d1 days.
#    - Must be 4 days, hence we set: d1 == 4.
#
# 2. Warsaw segment:
#    - Runs from Day d1 to Day d2.
#    - Duration = d2 - d1 + 1 days.
#    - Must be 4 days, so: d2 - d1 + 1 == 4.
#      With d1 == 4, this implies d2 == 7.
#
# 3. Bucharest segment:
#    - Runs from Day d2 to Day 10.
#    - Duration = 10 - d2 + 1 days.
#    - Must be 4 days, so: 10 - d2 + 1 == 4, which simplifies to d2 == 7.
#
# Moreover, since the annual show in Helsinki is on Days 1 through 4, having Helsinki segment exactly
# cover Day 1 to Day 4 meets that requirement.
#
# Now, we model these constraints using Z3.

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Helsinki to Warsaw.
d2 = Int('d2')  # Flight day from Warsaw to Bucharest.

# Constraint for Helsinki: 4 days.
s.add(d1 == 4)

# Constraint for Warsaw: 4 days.
s.add(d2 - d1 + 1 == 4)

# Constraint for Bucharest: 4 days.
s.add(10 - d2 + 1 == 4)

# Enforce ordering and validity:
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 10)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 4 (Helsinki -> Warsaw flight on Day 4)
    d2_val = m[d2].as_long()  # Expected: 7 (Warsaw -> Bucharest flight on Day 7)
    
    print("Trip plan found:\n")
    
    # Helsinki segment.
    print("1. Stay in Helsinki from Day 1 to Day {} (4 days).".format(d1_val))
    print("   -> Attend the annual show in Helsinki (Days 1 to 4).")
    print("   -> On Day {}, take a direct flight from Helsinki to Warsaw.".format(d1_val))
    
    # Warsaw segment.
    print("2. Stay in Warsaw from Day {} to Day {} (4 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Warsaw to Bucharest.".format(d2_val))
    
    # Bucharest segment.
    print("3. Stay in Bucharest from Day {} to Day 10 (4 days).".format(d2_val))
else:
    print("No solution exists!")