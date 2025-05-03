from z3 import *

# We have a 14-day trip and 3 cities with the following direct flight connections:
#   • A direct flight from Zurich to Istanbul.
#   • A direct flight from Istanbul to Tallinn.
#   • (Also, a direct flight from Zurich to Tallinn exists, but it is not used in our chosen itinerary.)
#
# Itinerary requirements:
#   - Spend 7 days in Zurich.
#   - Spend 5 days in Istanbul.
#   - Spend 4 days in Tallinn.
#
# Additional constraint:
#   - From day 1 to day 7 there is an annual show in Zurich, so you must be in Zurich during that period.
#
# We model the itinerary as a sequence of two flight transitions:
#   Let:
#     d1 = the flight day when you leave City1 and go to City2.
#     d2 = the flight day when you leave City2 and go to City3.
#
# In our chosen itinerary order we set:
#   City1 = Zurich (to cover the show, with 7 days)
#   City2 = Istanbul (5 days)
#   City3 = Tallinn (4 days)
#
# With the convention (flight day counts in both the departing and arriving cities):
#
#   Duration in City1 = d1, which must equal 7.
#
#   Duration in City2 = d2 - d1 + 1, which must equal 5.
#
#   Duration in City3 = 14 - d2 + 1, which must equal 4.
#
# Let’s solve these equations:
#
#   From City1: d1 = 7.
#
#   From City2: d2 - 7 + 1 = 5   ->   d2 - 6 = 5    ->   d2 = 11.
#
#   From City3: 14 - d2 + 1 = 15 - d2 must equal 4   ->   15 - d2 = 4   ->  d2 = 11.
#
# Thus we obtain d1 = 7 and d2 = 11.
#
# The itinerary is then:
#
#   1. Stay in Zurich from Day 1 to Day 7 (7 days) and attend the annual show during days 1 to 7.
#      On Day 7, take a direct flight from Zurich to Istanbul.
#
#   2. Stay in Istanbul from Day 7 to Day 11 (5 days).
#      On Day 11, take a direct flight from Istanbul to Tallinn.
#
#   3. Stay in Tallinn from Day 11 to Day 14 (4 days).
#
# This plan obeys the direct flight availability:
#   - Zurich -> Istanbul is available.
#   - Istanbul -> Tallinn is available.
#
# Now we encode these constraints using Z3:

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Zurich (City1) to Istanbul (City2).
d2 = Int('d2')  # Flight day from Istanbul (City2) to Tallinn (City3).

# City durations based on flight days (inclusive counting):
#   Duration in City1 (Zurich) = d1  ==> must equal 7 days.
#   Duration in City2 (Istanbul) = d2 - d1 + 1  ==> must equal 5 days.
#   Duration in City3 (Tallinn) = 14 - d2 + 1 = 15 - d2  ==> must equal 4 days.
s.add(d1 == 7)
s.add(d2 - d1 + 1 == 5)
s.add(15 - d2 == 4)

# Enforce flight order and that flight days fall within the trip span:
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 14)

# The annual show in Zurich must be attended from Day 1 to Day 7.
# Since Zurich is City1 and occupied from Day 1 to Day d1, d1 = 7 ensures that you are in Zurich exactly during the show period.

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Should be 7.
    d2_val = m[d2].as_long()  # Should be 11.
    
    print("Trip plan found:\n")
    print("1. Stay in Zurich from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> Attend the annual show in Zurich during days 1 to 7.")
    print("   -> On Day {}, take a direct flight from Zurich to Istanbul.".format(d1_val))
    print("2. Stay in Istanbul from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Istanbul to Tallinn.".format(d2_val))
    print("3. Stay in Tallinn from Day {} to Day 14 (4 days).".format(d2_val))
else:
    print("No solution exists!")