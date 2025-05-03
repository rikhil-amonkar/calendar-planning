from z3 import *

# We have a 10-day trip and 3 cities with required durations:
#   Riga:      3 days
#   Paris:     4 days
#   Reykjavik: 5 days (and an annual show in Reykjavik from Day 6 to Day 10)
#
# The available direct flights are between:
#   Riga and Paris, and between Paris and Reykjavik.
#
# Since there is no direct flight between Riga and Reykjavik,
# one acceptable itinerary is to travel in the order:
#   Riga -> Paris -> Reykjavik.
#
# We denote:
#   d1 = the flight day from Riga to Paris.
#   d2 = the flight day from Paris to Reykjavik.
#
# When counting days, the flight day is shared by both the departure and arrival cities.
#
# Therefore, the time spent in each city is modeled as:
#
#   Riga:      Days 1 to d1,            Total = d1 days  ==> d1 must equal 3.
#
#   Paris:     Days d1 to d2,            Total = d2 - d1 + 1 days  ==> must equal 4.
#
#   Reykjavik: Days d2 to 10,             Total = 10 - d2 + 1 = 11 - d2 days  ==> must equal 5.
#
# In equations:
#   d1 = 3,
#   d2 - d1 + 1 = 4   --> d2 - 3 + 1 = 4  --> d2 = 6,
#   and 11 - d2 = 5  --> 11 - 6 = 5.
#
# The annual show in Reykjavik is held from Day 6 to Day 10.
# In this itinerary, you arrive in Reykjavik on Day d2 = 6 and remain
# there through Day 10, fulfilling the show requirement.
#
# Now we encode the problem in Z3:

s = Solver()

# Define integer variables for the flight days:
d1 = Int('d1')  # Flight day from Riga to Paris.
d2 = Int('d2')  # Flight day from Paris to Reykjavik.

# Set the constraints based on the city durations:
s.add(d1 == 3)                # Riga: Stay exactly 3 days (Days 1 to 3).
s.add(d2 - d1 + 1 == 4)         # Paris: Stay exactly 4 days (Days d1 to d2).
s.add(11 - d2 == 5)             # Reykjavik: Stay exactly 5 days (Days d2 to 10).

# Enforce the chronological order of flights:
s.add(d1 < d2)

# Ensure the flight days are within the trip’s 10 days:
s.add(d1 >= 1, d2 <= 10)

# The annual show in Reykjavik is from Day 6 to Day 10.
# Since the itinerary guarantees being in Reykjavik from Day d2 to Day 10,
# and d2 = 6, the show constraint is satisfied.
s.add(d2 >= 6)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected value: 3.
    d2_val = m[d2].as_long()  # Expected value: 6.

    print("Trip plan found:\n")
    print("1. Stay in Riga from Day 1 to Day {} (3 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Riga to Paris.".format(d1_val))
    print("2. Stay in Paris from Day {} to Day {} (4 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Paris to Reykjavik.".format(d2_val))
    print("3. Stay in Reykjavik from Day {} to Day 10 (5 days).".format(d2_val))
    print("   -> Attend the annual show in Reykjavik from Day 6 to Day 10.")
else:
    print("No solution exists!")