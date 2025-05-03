from z3 import *

# In this problem, the available direct flights connect:
#   • Manchester and Bucharest
#   • Bucharest and Lyon
#
# This suggests a feasible itinerary order of:
#   Manchester -> Bucharest -> Lyon
#
# We plan the trip over 17 days and define two flight days:
#   d1: the day when you fly from Manchester to Bucharest. 
#       (Manchester is visited from Day 1 to Day d1)
#   d2: the day when you fly from Bucharest to Lyon.
#       (Bucharest is visited from Day d1 to Day d2)
#
# The remaining leg, Lyon, is then visited from Day d2 to Day 17.
#
# The requirements are:
#   • Manchester for 7 days:
#         Manchester leg: d1 days, so d1 must be 7.
#   • Bucharest for 7 days:
#         Bucharest leg: d2 - d1 + 1 days, so d2 - d1 + 1 must be 7.
#         With d1 = 7, this implies: d2 - 7 + 1 = 7, so d2 = 13.
#   • Lyon for 5 days:
#         Lyon leg: 17 - d2 + 1 days, so 18 - d2 must be 5.
#         This again yields d2 = 13.
#
# In addition, you plan to visit relatives in Lyon between day 13 and day 17.
# Since the Lyon leg (Day 13 to Day 17) falls exactly in that period, the condition is satisfied.
#
# Now we set up and solve these constraints with Z3.

s = Solver()

# Define flight switching day variables:
d1 = Int('d1')  # Day to fly from Manchester to Bucharest
d2 = Int('d2')  # Day to fly from Bucharest to Lyon

# Add constraints based on duration requirements:
s.add(d1 == 7)                # Manchester leg must last 7 days
s.add(d2 - d1 + 1 == 7)         # Bucharest leg must last 7 days, which implies d2 == 13 when d1 == 7
s.add(18 - d2 == 5)            # Lyon leg must last 5 days, i.e., 18 - d2 = 5  ==> d2 = 13

# Enforce timeline order:
s.add(d1 < d2)    # You must fly from Manchester to Bucharest before flying from Bucharest to Lyon.
s.add(d1 >= 1, d2 <= 17)  # Flight days are within the trip period

# Check for a solution:
if s.check() == sat:
    model = s.model()
    d1_val = model[d1].as_long()  # expected to be 7
    d2_val = model[d2].as_long()  # expected to be 13

    print("Trip plan found:\n")
    print("1. Stay in Manchester from Day 1 to Day {} (7 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Manchester to Bucharest.".format(d1_val))
    print("2. Stay in Bucharest from Day {} to Day {} (7 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Bucharest to Lyon.".format(d2_val))
    print("3. Stay in Lyon from Day {} to Day 17 (5 days).".format(d2_val))
    print("   -> Visit your relatives in Lyon between Day 13 and Day 17.")
else:
    print("No solution exists!")