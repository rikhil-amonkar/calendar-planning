from z3 import *

# We plan a 10‑day trip visiting the following 3 cities with these requirements:
#   • Reykjavik: 6 days.
#   • Milan:     4 days.
#   • Porto:     2 days.
#
# There is an annual show in Porto from Day 9 to Day 10 which must be attended.
#
# The available direct flights are:
#   • from Reykjavik to Milan,
#   • from Milan to Porto.
#
# We assume the following flight plan:
#   Reykjavik -> Milan -> Porto.
#
# We use the convention that when you take a flight on a day, that day counts as the last day in the
# departure city and the first day in the arrival city.
#
# Let:
#   d1: the flight day from Reykjavik to Milan.
#   d2: the flight day from Milan to Porto.
#
# Then the durations in each city are:
#   - Reykjavik: Days 1 to d1, duration = d1 days.
#   - Milan: Days d1 to d2, duration = d2 - d1 + 1 days.
#   - Porto: Days d2 to Day 10, duration = 10 - d2 + 1 = 11 - d2 days.
#
# We require:
#   Reykjavik: d1 == 6      (6 days in Reykjavik),
#   Milan:     d2 - d1 + 1 == 4   --> d2 - 6 + 1 == 4, so d2 == 9,
#   Porto:     11 - d2 == 2        --> 11 - 9 = 2 days in Porto.
#
# The show in Porto falls from Day 9 to Day 10 and Porto is visited from Day 9 (d2) to Day 10, which meets the show constraint.
#
# Let's set up these constraints in Z3:
s = Solver()

# Define flight day variables.
d1 = Int('d1')  # Flight day from Reykjavik to Milan.
d2 = Int('d2')  # Flight day from Milan to Porto.

# Add the constraints for the durations in each city.
s.add(d1 == 6)                      # Reykjavik must be visited for 6 days (Days 1 to 6).
s.add(d2 - d1 + 1 == 4)               # Milan must be visited for 4 days.
s.add(11 - d2 == 2)                   # Porto must be visited for 2 days.
  
# Flight order and domain constraints.
s.add(d1 < d2)        # The flight from Reykjavik to Milan occurs before the flight from Milan to Porto.
s.add(d1 >= 1, d2 <= 10)  # Flight days must be within the overall 10-day period.

# The annual show in Porto from Day 9 to Day 10 is satisfied because the visit to Porto is from d2 (which will be Day 9) to Day 10.

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 6
    d2_val = m[d2].as_long()  # Expected: 9

    print("Trip plan found:\n")
    print("1. Stay in Reykjavik from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Reykjavik to Milan.".format(d1_val))
    print("2. Stay in Milan from Day {} to Day {} (4 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Milan to Porto.".format(d2_val))
    print("3. Stay in Porto from Day {} to Day 10 (2 days).".format(d2_val))
    print("   -> Attend the annual show in Porto from Day 9 to Day 10.")
else:
    print("No solution exists!")