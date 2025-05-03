from z3 import *

# In this problem, we have 3 cities and available direct flights:
#   • A direct flight exists between Istanbul and Budapest.
#   • A direct flight exists from Dubrovnik to Istanbul.
#
# These flights force an itinerary order:
#    Dubrovnik -> Istanbul -> Budapest
#
# We plan a 12-day trip.
#
# Let:
#   d1: the day when you take the direct flight from Dubrovnik to Istanbul.
#       Thus, you are in Dubrovnik from Day 1 to Day d1.
#
#   d2: the day when you take the direct flight from Istanbul to Budapest.
#       Thus, you are in Istanbul from Day d1 to Day d2, and 
#       you are in Budapest from Day d2 to Day 12.
#
# The requirements are:
# 1. Spend 3 days in Dubrovnik.
#    => Dubrovnik leg duration = d1. So, d1 == 3.
#
# 2. Spend 5 days in Istanbul.
#    => Istanbul leg duration = d2 - d1 + 1.
#       So, d2 - d1 + 1 == 5.
#
# 3. Spend 6 days in Budapest.
#    => Budapest leg duration = 12 - d2 + 1 = 13 - d2.
#       So, 13 - d2 == 6.
#
# Solving these:
#   From (1):         d1 = 3.
#   From (3):         13 - d2 == 6  => d2 = 7.
#   Check (2):        d2 - 3 + 1 = 7 - 3 + 1 = 5. (✔)
#
# Thus, the itinerary is:
#   Dubrovnik: Days 1   to 3   (3 days)
#   Istanbul:  Days 3   to 7   (5 days)
#   Budapest:  Days 7   to 12  (6 days)
#
# We now encode this using Z3.
s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Day of flight from Dubrovnik to Istanbul.
d2 = Int('d2')  # Day of flight from Istanbul to Budapest.

# Add constraints for the required durations:
s.add(d1 == 3)                # Dubrovnik for 3 days.
s.add(d2 - d1 + 1 == 5)         # Istanbul for 5 days.
s.add(13 - d2 == 6)             # Budapest for 6 days.

# Enforce flight order and trip bounds:
s.add(d1 < d2)                # Must fly from Dubrovnik to Istanbul before Istanbul to Budapest.
s.add(d1 >= 1, d2 <= 12)        # Flight days fall within the 12-day trip.

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # Should be 3
    d2_val = model[d2].as_long()  # Should be 7

    print("Trip plan found:\n")
    print("1. Stay in Dubrovnik from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Dubrovnik to Istanbul.".format(d1_val))
    print("2. Stay in Istanbul from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Istanbul to Budapest.".format(d2_val))
    print("3. Stay in Budapest from Day {} to Day 12 (6 days).".format(d2_val))
else:
    print("No solution exists!")