from z3 import *

# We have a 11-day trip visiting 3 cities with the following requirements:
#   • Bucharest: 6 days.
#   • Brussels: 3 days.
#   • Krakow: 4 days, and from Day 8 to Day 11 there is an annual show in Krakow.
#
# If we add the durations we get 6 + 3 + 4 = 13 days.
# However, by overlapping the flight days (each flight day counts as both the last day
# in the city you are leaving and the first day in the city you are arriving), we can fit the itinerary in 11 days.
#
# Available direct flights:
#   • between Bucharest and Brussels,
#   • between Brussels and Krakow.
#
# We select the itinerary order:
#   Bucharest -> Brussels -> Krakow
#
# Let:
#   d1 = flight day from Bucharest to Brussels.
#   d2 = flight day from Brussels to Krakow.
#
# Then:
#
# 1. Bucharest segment:
#    - Runs from Day 1 to Day d1.
#    - Duration = d1 days.
#    - Must be 6 days, so: d1 == 6.
#
# 2. Brussels segment:
#    - Runs from Day d1 to Day d2.
#    - Duration = d2 - d1 + 1 days.
#    - Must be 3 days, so: d2 - d1 + 1 == 3.
#
# 3. Krakow segment:
#    - Runs from Day d2 to Day 11.
#    - Duration = 11 - d2 + 1 days.
#    - Must be 4 days, so: 11 - d2 + 1 == 4.
#
# For the Krakow segment, notice that the annual show runs from Day 8 to Day 11.
# Hence, we need the Krakow segment to cover exactly these days, which directs d2 to Day 8.
#
# Now we model these constraints in Z3.
s = Solver()

# Define flight day variables:
d1 = Int('d1')  # Flight from Bucharest to Brussels.
d2 = Int('d2')  # Flight from Brussels to Krakow.

# Constraint 1: Bucharest segment must last 6 days.
s.add(d1 == 6)

# Constraint 2: Brussels segment must last 3 days.
s.add(d2 - d1 + 1 == 3)

# Constraint 3: Krakow segment must last 4 days.
s.add(11 - d2 + 1 == 4)

# Enforce ordering and valid day bounds.
s.add(d1 < d2)
s.add(d1 >= 1, d2 <= 11)

if s.check() == sat:
    m = s.model()
    d1_val = m[d1].as_long()  # Expected: 6 (flight from Bucharest to Brussels on Day 6)
    d2_val = m[d2].as_long()  # Expected: 8 (flight from Brussels to Krakow on Day 8)
    
    print("Trip plan found:\n")
    
    # Bucharest segment.
    print("1. Stay in Bucharest from Day 1 to Day {} (6 days).".format(d1_val))
    print("   -> On Day {}, take a direct flight from Bucharest to Brussels.".format(d1_val))
    
    # Brussels segment.
    print("2. Stay in Brussels from Day {} to Day {} (3 days).".format(d1_val, d2_val))
    print("   -> On Day {}, take a direct flight from Brussels to Krakow.".format(d2_val))
    
    # Krakow segment.
    print("3. Stay in Krakow from Day {} to Day 11 (4 days).".format(d2_val))
    print("   -> Attend the annual show in Krakow from Day 8 to Day 11.")
else:
    print("No solution exists!")