from z3 import *

# We have a 10-day trip with 3 cities in this order:
#   City 1: Split     (7 days required)
#   City 2: Frankfurt  (2 days required)
#   City 3: Reykjavik  (3 days required, with a workshop between day 8 and day 10)
#
# The available direct flights are:
#   • A flight between Split and Frankfurt.
#   • A flight between Frankfurt and Reykjavik.
#
# We use the standard convention that the day on which a flight is taken counts 
# as a day spent in both the departing city and the arriving city.
#
# Let:
#   d1 = the flight day from Split to Frankfurt.
#   d2 = the flight day from Frankfurt to Reykjavik.
#
# Then the stay durations are:
#   In Split:     Days 1 to d1         => d1 days (should equal 7).
#   In Frankfurt: Days d1 to d2         => d2 - d1 + 1 days (should equal 2).
#   In Reykjavik: Days d2 to 10          => 10 - d2 + 1 = 11 - d2 days (should equal 3).
#
# Let’s set up the equations:
#
#   d1                   = 7.
#   d2 - d1 + 1          = 2   =>   d2 - 7 + 1 = 2  =>  d2 = 8.
#   11 - d2              = 3   =>   11 - 8 = 3. 
#
# This yields d1 = 7 and d2 = 8.
#
# The workshop in Reykjavik is between day 8 and day 10.
# In this plan, you will be in Reykjavik from day 8 to day 10,
# satisfying the workshop constraint.
#
# Now we encode these constraints into a Z3 model:

s = Solver()

# Flight day variables:
d1 = Int('d1')  # Flight day from Split to Frankfurt.
d2 = Int('d2')  # Flight day from Frankfurt to Reykjavik.

# Add constraints based on the duration requirements:
s.add(d1 == 7)                 # Split stay duration = 7 days.
s.add(d2 - d1 + 1 == 2)          # Frankfurt stay duration = 2 days.
s.add(11 - d2 == 3)              # Reykjavik stay duration = 3 days.

# Enforce flight ordering and that the flight days lie within the 10-day trip:
s.add(d1 < d2)                 # Must fly to Reykjavik after Frankfurt.
s.add(d1 >= 1, d2 <= 10)

# The workshop in Reykjavik is between day 8 and day 10.
# Since you'll be in Reykjavik from day d2 to day 10, and d2 = 8, this condition is met.
s.add(d2 >= 8)  # This ensures you're in Reykjavik at the start of the workshop window.

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected 7.
    d2_val = m[d2].as_long()  # Expected 8.
    
    print("Trip plan found:\n")
    print("1. Stay in Split from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Split to Frankfurt.".format(d1_val))
    print("2. Stay in Frankfurt from Day {} to Day {} (2 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Frankfurt to Reykjavik.".format(d2_val))
    print("3. Stay in Reykjavik from Day {} to Day 10 (3 days).".format(d2_val))
    print("   -> Attend the workshop in Reykjavik between Day 8 and Day 10.")
else:
    print("No solution exists!")