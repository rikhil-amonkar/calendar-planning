from z3 import *

# We have a 10-day trip with 3 cities:
#   • Dubrovnik, Frankfurt, and Krakow.
# Available direct flights are:
#   • Dubrovnik and Frankfurt, and
#   • Frankfurt and Krakow.
#
# Requirements:
#   - Stay in Dubrovnik for 7 days.
#   - Visit Frankfurt for 3 days.
#   - Spend 2 days in Krakow.
#
# Additional constraint:
#   - Attend a wedding in Krakow between day 9 and day 10.
#
# One viable itinerary order is:
#   1. Start in Dubrovnik.
#   2. Fly from Dubrovnik to Frankfurt.
#   3. Fly from Frankfurt to Krakow, so that the Krakow visit covers day 9-10.
#
# We model the itinerary using two flight transitions:
#   d1: the flight day from Dubrovnik to Frankfurt.
#       You are in Dubrovnik from Day 1 to Day d1 (inclusive), and so the duration in Dubrovnik = d1.
#
#   d2: the flight day from Frankfurt to Krakow.
#       You are in Frankfurt from Day d1 to Day d2 (inclusive), with duration = d2 - d1 + 1,
#       and in Krakow from Day d2 to Day 10 (inclusive), with duration = 10 - d2 + 1.
#
# Using the duration requirements:
#   Dubrovnik: d1 = 7.
#   Frankfurt: d2 - d1 + 1 = 3  =>  d2 - 7 + 1 = 3  =>  d2 - 6 = 3  =>  d2 = 9.
#   Krakow: 10 - d2 + 1 = 11 - d2 should equal 2  =>  11 - d2 = 2  =>  d2 = 9.
#
# With d2 = 9, the Krakow visit covers days 9 and 10, satisfying the wedding requirement.
#
# Now we encode these constraints using Z3:

s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight day from Dubrovnik to Frankfurt.
d2 = Int('d2')  # Flight day from Frankfurt to Krakow.

# Add constraints for durations in each city:
s.add(d1 == 7)              # Spend 7 days in Dubrovnik (Days 1..7).
s.add(d2 - d1 + 1 == 3)       # Spend 3 days in Frankfurt.
s.add(11 - d2 == 2)           # Spend 2 days in Krakow.

# Enforce flight ordering and bounds:
s.add(d1 < d2)              # Must take the flight from Frankfurt to Krakow after arriving from Dubrovnik.
s.add(d1 >= 1, d2 <= 10)      # d1 and d2 must be within the 10-day trip.

# The wedding in Krakow must occur between day 9 and day 10.
# Since we are in Krakow from day d2 to day 10, we require d2 <= 9.
s.add(d2 <= 9)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected d1 = 7.
    d2_val = m[d2].as_long()  # Expected d2 = 9.
    
    print("Trip plan found:\n")
    print("1. Stay in Dubrovnik from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Dubrovnik to Frankfurt.".format(d1_val))
    print("2. Stay in Frankfurt from Day {} to Day {} (3 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Frankfurt to Krakow.".format(d2_val))
    print("3. Stay in Krakow from Day {} to Day 10 (2 days).".format(d2_val))
    print("   -> Attend the wedding in Krakow between Day 9 and Day 10.")
else:
    print("No solution exists!")