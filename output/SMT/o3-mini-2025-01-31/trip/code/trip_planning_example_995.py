from z3 import *

# City indices and names:
# 0: Oslo        (2 days; event: meet friends in Oslo between day 3 and day 4)
# 1: Stuttgart   (3 days)
# 2: Venice      (4 days)
# 3: Split       (4 days)
# 4: Barcelona   (3 days; event: annual show in Barcelona from day 1 to day 3)
# 5: Brussels    (3 days; event: meet a friend in Brussels between day 9 and day 11)
# 6: Copenhagen  (3 days)
city_names = ["Oslo", "Stuttgart", "Venice", "Split", "Barcelona", "Brussels", "Copenhagen"]

# Required days per city:
req = [2, 3, 4, 4, 3, 3, 3]
# Total required contributions = 2+3+4+4+3+3+3 = 22.
# Base days = 16.
# Each flight day (when a flight occurs) contributes an extra count (both departure and arrival).
# Hence, 16 + (#flights) = 22 => #flights = 6.
# This splits the itinerary into 7 segments (one for each visited city).

# Allowed direct flights (bidirectional):
allowed_flights = [
    # Venice and Stuttgart
    (2, 1), (1, 2),
    # Oslo and Brussels
    (0, 5), (5, 0),
    # Split and Copenhagen
    (3, 6), (6, 3),
    # Barcelona and Copenhagen
    (4, 6), (6, 4),
    # Barcelona and Venice
    (4, 2), (2, 4),
    # Brussels and Venice
    (5, 2), (2, 5),
    # Barcelona and Stuttgart
    (4, 1), (1, 4),
    # Copenhagen and Brussels
    (6, 5), (5, 6),
    # Oslo and Split
    (0, 3), (3, 0),
    # Oslo and Venice
    (0, 2), (2, 0),
    # Barcelona and Split
    (4, 3), (3, 4),
    # Oslo and Copenhagen
    (0, 6), (6, 0),
    # Barcelona and Oslo
    (4, 0), (0, 4),
    # Copenhagen and Stuttgart
    (6, 1), (1, 6),
    # Split and Stuttgart
    (3, 1), (1, 3),
    # Copenhagen and Venice
    (6, 2), (2, 6),
    # Barcelona and Brussels
    (4, 5), (5, 4),
]

# Total base days in the itinerary:
DAYS = 16

# Create Z3 variables:
# c[d] represents the base city on day d (0-indexed: day d corresponds to day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable indicating whether a flight occurs on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates that day d is the start of a new segment (day 0 is always a segment start).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be one of the 7 cities (0 through 6).
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 7)

# Day 0 is the start of a new segment.
s.add(isSeg[0] == True)

# For each day d from 1 to DAYS-1:
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, then the flight from c[d-1] to c[d] must be allowed.
    s.add(Implies(flight[d], 
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 6 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# The starting city of each segment (day 0 and any day with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that every city is visited at least once.
for city in range(7):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# Day 0 contributes 1 for c[0]. For each day d from 1 to DAYS-1:
#   - If a flight occurs on day d, then day d contributes 1 to both c[d-1] and c[d];
#   - Otherwise, it contributes 1 to c[d] only.
counts = [Int(f"count_{city}") for city in range(7)]
for city in range(7):
    init = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(daily))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay(d, target)
# Returns a constraint saying that on day d the itinerary "includes" the target city.
# If a flight occurs on day d, then the day counts for both the departure (c[d-1]) and arrival (c[d]).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Meet friends in Oslo (city 0) between day 3 and day 4.
#    Day 3 and day 4 correspond to indices 2 and 3.
oslo_friend = [inCityOnDay(d, 0) for d in [2, 3]]
s.add(Or(oslo_friend))

# 2. Annual show in Barcelona (city 4) from day 1 to day 3.
#    Days 1 to 3 correspond to indices 0, 1, and 2.
barcelona_show = [inCityOnDay(d, 4) for d in [0, 1, 2]]
s.add(Or(barcelona_show))

# 3. Meet a friend in Brussels (city 5) between day 9 and day 11.
#    Days 9 to 11 correspond to indices 8, 9, and 10.
brussels_friend = [inCityOnDay(d, 5) for d in [8, 9, 10]]
s.add(Or(brussels_friend))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[base]}"
        # If a flight occurs on this day, include flight information.
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for i in range(7):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")