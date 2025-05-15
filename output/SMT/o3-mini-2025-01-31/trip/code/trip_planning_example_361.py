from z3 import *

# City indices and names:
# 0: Paris      (6 days)
# 1: Madrid     (7 days; event: annual show in Madrid from day 1 to day 7)
# 2: Bucharest  (2 days; event: visit relatives in Bucharest between day 14 and day 15)
# 3: Seville    (3 days)
city_names = ["Paris", "Madrid", "Bucharest", "Seville"]

# Required day contributions:
# Paris: 6, Madrid: 7, Bucharest: 2, Seville: 3
# Total required = 6 + 7 + 2 + 3 = 18.
req = [6, 7, 2, 3]

# We have 15 base days.
# A flight day, when a flight occurs, counts for both departure and arrival.
# So total contributions = base_days + (#flights)
# => 15 + (#flights) = 18
# Thus, exactly 3 flights must occur.
# This partitions the itinerary into 4 segments (one for each visited city).

# Allowed direct flights (bidirectional unless noted):
# Paris and Bucharest, Seville and Paris, Madrid and Bucharest, Madrid and Paris, Madrid and Seville.
allowed_flights = [
    (0, 2), (2, 0),  # Paris <-> Bucharest
    (3, 0), (0, 3),  # Seville <-> Paris
    (1, 2), (2, 1),  # Madrid <-> Bucharest
    (1, 0), (0, 1),  # Madrid <-> Paris
    (1, 3), (3, 1)   # Madrid <-> Seville
]

DAYS = 15  # number of base days

# Create Z3 variables.
# c[d] represents the base city on day d (0-indexed: day d corresponds to day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Bool indicating whether a flight occurs on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 always is).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day, the base city must be in {0,1,2,3}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 4)

# Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flights and segments.
for d in range(1, DAYS):
    # A flight occurs when the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, then the flight route must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# There must be exactly 3 flights.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 3)

# The starting city of each segment (day 0 and any day with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that every city is visited at least once.
for city in range(4):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Calculate day contributions for each city.
# - Day 0 contributes 1 to the city c[0].
# - For each day d (1 to DAYS-1):
#     if a flight happens on day d, contribute 1 to both c[d-1] and c[d];
#     else contribute 1 to c[d] only.
counts = [Int(f"count_{city}") for city in range(4)]
for city in range(4):
    init = If(c[0] == city, 1, 0)
    day_contrib = []
    for d in range(1, DAYS):
        day_contrib.append(
            If(flight[d],
               (If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0)),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(day_contrib))
    s.add(counts[city] == req[city])

# Helper function: returns a constraint that the itinerary "includes" target city on day d.
# If a flight occurs on day d, both the departure (c[d-1]) and arrival (c[d]) are counted.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Annual show in Madrid (city 1) from day 1 to day 7.
#    Days 1 to 7 correspond to indices 0 through 6.
annual_show_madrid = [inCityOnDay(d, 1) for d in range(0, 7)]
s.add(Or(annual_show_madrid))

# 2. Visit relatives in Bucharest (city 2) between day 14 and day 15.
#    Days 14 and 15 correspond to indices 13 and 14.
relatives_bucharest = [inCityOnDay(d, 2) for d in [13, 14]]
s.add(Or(relatives_bucharest))

# Check for solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(4):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")