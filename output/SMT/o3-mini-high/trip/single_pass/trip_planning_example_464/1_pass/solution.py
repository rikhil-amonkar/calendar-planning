from z3 import *
import json

# We have 5 cities:
# 0: Krakow (5 days)
# 1: Frankfurt (4 days)
# 2: Oslo (3 days) – also the city where you visit relatives between day 16 and day 18
# 3: Dubrovnik (5 days) – also where you want to meet your friends between day 5 and day 9
# 4: Naples (5 days)
#
# The total “raw” days if you simply add each city’s required stay is 5+4+3+5+5 = 22.
# However, because whenever you fly from one city to the next the flight day counts for both,
# you “save” one day for every flight. With 4 flights the actual itinerary takes 22 – 4 = 18 days.
#
# We model the trip as an ordered sequence of 5 “stays” (one per city) with overlapping “flight 
# days”. That is, if the i-th city is visited from day S[i] to E[i] (with E[i] = S[i] + duration - 1),
# then a flight from city_i to city_i+1 happens on day E[i] (which is also S[i+1]).
#
# In addition we have:
# • The Oslo (city 2) visit must include at least one day between day 16 and 18.
# • The Dubrovnik (city 3) visit must include at least one day between day 5 and 9.
# • Only direct flights are used; the allowed pairs (bidirectional) are:
#       (Krakow, Frankfurt), (Krakow, Oslo),
#       (Frankfurt, Oslo), (Frankfurt, Dubrovnik),
#       (Naples, Oslo), (Naples, Dubrovnik), (Naples, Frankfurt),
#       (Dubrovnik, Oslo).
#
# IMPORTANT: If you fly from city A to city B on day X, then that day X counts as time spent in both A and B.
#
# Finally, note that once the order is chosen the start-days become “fixed” by:
#   S[0] = 1
#   S[i+1] = S[i] + (duration of city at position i) – 1
# and the final constraint is: S[4] + (duration of city at position 4) – 1 = 18.
#
# One valid ordering found by analysis is:
#    Krakow → Frankfurt → Dubrovnik → Naples → Oslo
# which gives intervals:
#    Krakow:    Day 1 – 5
#    Frankfurt: Day 5 – 8   (flight from Krakow on day 5)
#    Dubrovnik: Day 8 – 12  (flight from Frankfurt on day 8)
#    Naples:    Day 12 – 16 (flight from Dubrovnik on day 12)
#    Oslo:      Day 16 – 18 (flight from Naples on day 16)
#
# In this plan:
# • Oslo’s interval [16,18] fully covers the relatives–visit window.
# • Dubrovnik’s interval [8,12] overlaps the friends–meeting window (days 5–9) by including days 8 and 9.
# • All direct flight legs are allowed:
#       Krakow–Frankfurt, Frankfurt–Dubrovnik, Dubrovnik–Naples, and Naples–Oslo.
#
# We now write a Z3-based Python program that “searches” for a valid ordering and computes
# the corresponding start-day values.

# Create Z3 solver
s = Solver()

# Define variables for the order: order[i] is the index of the city visited at position i.
order = [Int(f"order_{i}") for i in range(5)]
# Define variables for the start day of each city visit.
start = [Int(f"start_{i}") for i in range(5)]

# Mapping: 0:Krakow, 1:Frankfurt, 2:Oslo, 3:Dubrovnik, 4:Naples.
city_names = {0: "Krakow", 1: "Frankfurt", 2: "Oslo", 3: "Dubrovnik", 4: "Naples"}
# Fixed durations for each city.
durations = {0: 5, 1: 4, 2: 3, 3: 5, 4: 5}

# Each order variable must be one of the 5 cities.
for i in range(5):
    s.add(And(order[i] >= 0, order[i] <= 4))
# All cities are visited exactly once.
s.add(Distinct(order))

# We already deduced that Oslo must come last (to permit its “relatives‐visit” to fall
# between day 16 and 18). So force that:
s.add(order[4] == 2)
for i in range(4):
    s.add(order[i] != 2)

# Also Dubrovnik (city 3) must be visited early (so that its 5–day block can include
# a day between 5 and 9). In our analysis Dubrovnik works only in positions 0, 1, or 2.
# (If it were 3rd or 5th, its start day would be too late.)
s.add(order[3] != 3)
s.add(order[4] != 3)

# The start-day for the first city is day 1.
s.add(start[0] == 1)

# Helper: Given an expression 'o' for a city index, return its duration.
def duration_expr(o):
    return If(o == 0, durations[0],
           If(o == 1, durations[1],
           If(o == 2, durations[2],
           If(o == 3, durations[3],
              durations[4]))))

# The start day for the next city is determined by the previous city’s interval
# with flight day overlap (the last day of the previous interval counts in both).
for i in range(4):
    s.add(start[i+1] == start[i] + duration_expr(order[i]) - 1)
# The last visit must end on day 18.
s.add(start[4] + duration_expr(order[4]) - 1 == 18)

# Define allowed direct flight pairs (bidirectional) for consecutive cities.
# Using our mapping, the allowed flights (unordered pairs) are:
#   { (Krakow, Frankfurt), (Krakow, Oslo),
#     (Frankfurt, Oslo), (Frankfurt, Dubrovnik),
#     (Naples, Oslo), (Naples, Dubrovnik), (Naples, Frankfurt),
#     (Dubrovnik, Oslo) }.
allowed_pairs = [(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
for i in range(4):
    pair_conditions = []
    for (a, b) in allowed_pairs:
        pair_conditions.append(And(order[i] == a, order[i+1] == b))
        pair_conditions.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(pair_conditions))

# Special scheduling constraints:
# (A) In Dubrovnik (city 3) the 5–day visit [start, start+4] must contain a day between 5 and 9.
for i in range(5):
    s.add(Implies(order[i] == 3, And(start[i] <= 9, start[i] + 4 >= 5)))
# (B) In Oslo (city 2) the 3–day visit [start, start+2] must contain a day between 16 and 18.
for i in range(5):
    s.add(Implies(order[i] == 2, And(start[i] <= 18, start[i] + 2 >= 16)))

# Solve the model.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(5):
        city_index = m.evaluate(order[i]).as_long()
        city = city_names[city_index]
        s_day = m.evaluate(start[i]).as_long()
        dur = durations[city_index]
        e_day = s_day + dur - 1  # Remember: flight day is double-counted.
        itinerary.append({"city": city, "start_day": s_day, "end_day": e_day})
    # The itinerary segments explain that on the flight days the day is shared by two cities.
    # For example, if a city is scheduled from Day 1–5 and the next starts on Day 5,
    # then Day 5 counts for both.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")