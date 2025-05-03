from z3 import *

# We have 3 cities and available direct flights:
#    Copenhagen <-> Vienna, and Vienna <-> Lyon.
#
# Thus the forced itinerary order is:
#    Copenhagen -> Vienna -> Lyon
#
# The trip lasts 11 days, and we define two flight days:
#    d1: the day when you take a direct flight from Copenhagen to Vienna.
#        This means you are in Copenhagen from Day 1 to Day d1.
#    d2: the day when you take a direct flight from Vienna to Lyon.
#        This means you are in Vienna from Day d1 to Day d2,
#        and in Lyon from Day d2 to Day 11.
#
# Note that the travel day is shared by both the city you depart from and the city you arrive in.
#
# Requirements:
# 1. Spend 5 days in Copenhagen.
#    => The Copenhagen leg is from Day 1 to d1, so d1 must equal 5.
#
# 2. Attend a conference in Copenhagen on Day 1 and Day 5.
#    => With Copenhagen scheduled from Day 1 to Day 5, both Day 1 and Day 5 are covered.
#
# 3. Stay in Vienna for 4 days.
#    => The Vienna leg has duration d2 - d1 + 1.
#       We require: d2 - d1 + 1 == 4.
#
# 4. Stay in Lyon for 4 days.
#    => The Lyon leg has duration from Day d2 to Day 11, that is, 11 - d2 + 1 = 12 - d2.
#       We require: 12 - d2 == 4.
#
# Solve for the flight days d1 and d2 with these constraints.

s = Solver()

# Define the flight day variables:
d1 = Int('d1')  # Flight day from Copenhagen to Vienna.
d2 = Int('d2')  # Flight day from Vienna to Lyon.

# Add constraints
s.add(d1 == 5)                      # Copenhagen for 5 days: Days 1 to 5.
s.add(d2 - d1 + 1 == 4)               # Vienna for 4 days.
s.add(12 - d2 == 4)                   # Lyon for 4 days.
s.add(d1 < d2)                      # Must fly from Copenhagen to Vienna before flying to Lyon.
s.add(d1 >= 1, d2 <= 11)              # Flight days must lie within the 11 day trip.

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # Expected to be 5
    d2_val = model[d2].as_long()  # Expected to be 8

    print("Trip plan found:\n")
    print("1. Stay in Copenhagen from Day 1 to Day {} (5 days).".format(d1_val))
    print("   -> Attend the conference in Copenhagen on Day 1 and Day 5.")
    print("   -> On Day {}, take a direct flight from Copenhagen to Vienna.".format(d1_val))
    print("2. Stay in Vienna from Day {} to Day {} ({} days).".format(d1_val, d2_val, d2_val - d1_val + 1))
    print("   -> On Day {}, take a direct flight from Vienna to Lyon.".format(d2_val))
    print("3. Stay in Lyon from Day {} to Day 11 ({} days).".format(d2_val, 12 - d2_val))
else:
    print("No solution exists!")