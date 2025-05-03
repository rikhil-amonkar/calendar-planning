from z3 import *

# We have 3 cities (itinerary order based on available direct flights):
#   Lyon -> Frankfurt -> Krakow
#
# The trip runs for 10 days. We introduce:
#   d1: the day of the direct flight from Lyon to Frankfurt 
#       (Lyon is visited from Day 1 to d1, inclusive)
#   d2: the day of the direct flight from Frankfurt to Krakow
#       (Frankfurt is visited from Day d1 to d2, inclusive)
#       (Krakow is visited from Day d2 to Day 10, inclusive)
#
# Remember that the travel day is counted for both the city you leave and the city you enter.
#
# The requirements are:
# 1. Spend 7 days in Lyon:
#    -> Duration in Lyon = d1, so we require  d1 == 7.
#
# 2. Spend 2 days in Frankfurt:
#    -> Duration in Frankfurt = d2 - d1 + 1, so we require d2 - d1 + 1 == 2.
#
# 3. Stay in Krakow for 3 days:
#    -> Duration in Krakow = (10 - d2 + 1) = 11 - d2, so we require 11 - d2 == 3.
#
# 4. There is an annual show in Krakow from Day 8 to Day 10.
#    -> With the above constraints, the Krakow leg will run from Day d2 to Day 10.
#       The constraint 11 - d2 == 3 forces d2 = 8,
#       so the Krakow visit will be exactly during Days 8, 9, and 10, covering the annual show.
#
# Now we solve these constraints using Z3.

s = Solver()

# Define the flight (transition) days:
d1 = Int('d1')  # Flight day from Lyon to Frankfurt
d2 = Int('d2')  # Flight day from Frankfurt to Krakow

# Add constraints based on the problem requirements:
s.add(d1 == 7)                 # Lyon for 7 days: Days 1 to 7.
s.add(d2 - d1 + 1 == 2)          # Frankfurt for 2 days.
s.add(11 - d2 == 3)              # Krakow for 3 days.

# Enforce ordering constraints:
s.add(d1 < d2)      # Must fly from Lyon to Frankfurt before Frankfurt to Krakow.
s.add(d1 >= 1, d2 <= 10)

# Check and print the solution:
if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # Expected to be 7
    d2_val = model[d2].as_long()  # Expected to be 8
    
    print("Trip plan found:\n")
    print("1. Stay in Lyon from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Lyon to Frankfurt.".format(d1_val))
    print("2. Stay in Frankfurt from Day {} to Day {} ({} days).".format(d1_val, d2_val, d2_val - d1_val + 1))
    print("   -> On Day {}, take a direct flight from Frankfurt to Krakow.".format(d2_val))
    print("3. Stay in Krakow from Day {} to Day 10 ({} days).".format(d2_val, 11 - d2_val))
    print("   -> Attend the annual show in Krakow from Day 8 to Day 10.")
else:
    print("No solution exists!")