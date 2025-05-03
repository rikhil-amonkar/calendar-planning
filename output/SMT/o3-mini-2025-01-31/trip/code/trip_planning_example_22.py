from z3 import *

# We have 3 cities, a total trip length of 11 days, and available direct flights:
# - A direct flight exists between Berlin and Frankfurt.
# - A direct flight exists between Frankfurt and Bucharest.
#
# The required durations for the cities are:
#   • Berlin for 7 days (and you must attend an annual show in Berlin from day 1 to day 7).
#   • Frankfurt for 4 days.
#   • Bucharest for 2 days.
#
# We construct an itinerary using two flight days:
#
# Let:
#   d1 = the day on which you fly from Berlin to Frankfurt.
#   d2 = the day on which you fly from Frankfurt to Bucharest.
#
# Following our convention:
#  - You are in Berlin from day 1 up to day d1.
#  - You are in Frankfurt from day d1 to day d2.
#  - You are in Bucharest from day d2 to day 11.
#
# The durations are defined as:
# 1. Berlin’s duration = d1      --> must equal 7.
# 2. Frankfurt’s duration = d2 - d1 + 1 --> must equal 4.
# 3. Bucharest’s duration = 11 - d2 + 1 = 12 - d2 --> must equal 2.
#
# Solving:
# - From (1): d1 = 7.
# - From (3): 12 - d2 = 2  --> d2 = 10.
# - Then Frankfurt’s duration: 10 - 7 + 1 = 4, which meets the requirement.
#
# The workshop (annual show) in Berlin is held from day 1 to day 7.
# In our plan, you are in Berlin until day 7 (inclusive). Therefore, you can attend the show.
#
# Now we encode the above constraints using Z3:

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Berlin to Frankfurt.
d2 = Int('d2')  # Flight day from Frankfurt to Bucharest.

# Add constraints for the durations:
s.add(d1 == 7)            # Berlin for 7 days: Day 1 to Day 7.
s.add(d2 - d1 + 1 == 4)     # Frankfurt for 4 days.
s.add(12 - d2 == 2)         # Bucharest for 2 days.

# Enforce proper flight ordering and that flight days lie within the 11-day trip.
s.add(d1 < d2)            # Must fly from Berlin to Frankfurt before Frankfurt to Bucharest.
s.add(d1 >= 1, d2 <= 11)    # Flight days are within Day 1 to Day 11.

# The show in Berlin is scheduled from day 1 to day 7.
# Since Berlin is visited from day 1 until day d1 and we have d1 = 7, the show requirement is met.
# (No extra constraint is needed besides the duration exactly matching 7 days for Berlin.)

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # Expect 7
    d2_val = model[d2].as_long()  # Expect 10

    print("Trip plan found:\n")
    print("1. Stay in Berlin from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> Attend the annual show in Berlin from Day 1 to Day 7.")
    print("   -> On Day {}, take a direct flight from Berlin to Frankfurt.".format(d1_val))
    print("2. Stay in Frankfurt from Day {} to Day {} (4 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Frankfurt to Bucharest.".format(d2_val))
    print("3. Stay in Bucharest from Day {} to Day 11 (2 days).".format(d2_val))
else:
    print("No solution exists!")