from z3 import *

# The available direct flights connect:
#   • Valencia and Amsterdam
#   • Amsterdam and Tallinn
#
# Therefore a valid itinerary order is: 
#   Valencia -> Amsterdam -> Tallinn
#
# We schedule the trip over 15 days and define:
#   d1: the day when you fly from Valencia to Amsterdam 
#       (i.e. the last day in Valencia and the first day in Amsterdam)
#   d2: the day when you fly from Amsterdam to Tallinn 
#       (i.e. the last day in Amsterdam and the first day in Tallinn)
#
# We assume:
#   - Valencia leg is from day 1 to day d1 (inclusive)
#   - Amsterdam leg is from day d1 to day d2 (inclusive)
#   - Tallinn leg is from day d2 to day 15 (inclusive)
#
# In our model, the durations are computed as:
#   • Valencia: d1 days (must equal 5)
#   • Amsterdam: (d2 - d1 + 1) days (must equal 5)
#   • Tallinn: (15 - d2 + 1) = (16 - d2) days (must equal 7)
#
# The given durations yield the following equations:
#   d1 = 5
#   d2 - d1 + 1 = 5  --> with d1 = 5, this gives d2 - 4 = 5, so d2 = 9
#   16 - d2 = 7     --> d2 = 9
#
# Also, you need to meet a friend in Tallinn between day 9 and day 15.
# Since Tallinn leg runs from day d2 (which is 9) to day 15, the friend meeting
# falls in that interval.
#
# Now we set up the Z3 solver with these constraints.

s = Solver()

# Define flight switching day variables.
d1 = Int('d1')   # Flight day from Valencia to Amsterdam.
d2 = Int('d2')   # Flight day from Amsterdam to Tallinn.

# Add constraints for durations:
s.add(d1 == 5)              # Valencia for 5 days: days 1 to 5.
s.add(d2 - d1 + 1 == 5)       # Amsterdam for 5 days.
s.add(16 - d2 == 7)           # Tallinn for 7 days.

# Enforce timeline order:
s.add(d1 < d2)      # Must fly from Valencia to Amsterdam before flying to Tallinn.
s.add(d1 >= 1, d2 <= 15)

# No extra constraint is needed for the friend meeting since Tallinn leg is from day 9 to 15.

if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # Expected to be 5.
    d2_val = model[d2].as_long()  # Expected to be 9.
    
    print("Trip plan found:\n")
    print("1. Stay in Valencia from Day 1 to Day {} (5 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Valencia to Amsterdam.".format(d1_val))
    print("2. Stay in Amsterdam from Day {} to Day {} (5 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Amsterdam to Tallinn.".format(d2_val))
    print("3. Stay in Tallinn from Day {} to Day 15 (7 days).".format(d2_val))
    print("   -> Meet your friend in Tallinn between Day 9 and Day 15.")
else:
    print("No solution exists!")