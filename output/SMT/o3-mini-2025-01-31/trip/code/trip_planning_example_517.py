from z3 import *

# Define cities and their required day contributions:
# 0: Dubrovnik   (5 days)
# 1: Warsaw      (2 days)
# 2: Stuttgart   (7 days; event: attend conference in Stuttgart on day 7 and day 13)
# 3: Bucharest   (6 days; event: attend wedding in Bucharest between day 1 and day 6)
# 4: Copenhagen  (3 days)
city_names = ["Dubrovnik", "Warsaw", "Stuttgart", "Bucharest", "Copenhagen"]
req = [5, 2, 7, 6, 3]  # required day contributions

# Total required contributions = 5+2+7+6+3 = 23.
# We have 19 base days. A flight day counts for both departure and arrival.
# Thus, #flights must equal 23 - 19 = 4.
# This implies 5 segments (one per city visited).

# Allowed direct flights (bidirectional):
# Warsaw <-> Copenhagen
# Stuttgart <-> Copenhagen
# Warsaw <-> Stuttgart
# Bucharest <-> Copenhagen
# Bucharest <-> Warsaw
# Copenhagen <-> Dubrovnik
allowed_flights = [
    (1, 4), (4, 1),        # Warsaw and Copenhagen
    (2, 4), (4, 2),        # Stuttgart and Copenhagen
    (1, 2), (2, 1),        # Warsaw and Stuttgart
    (3, 4), (4, 3),        # Bucharest and Copenhagen
    (3, 1), (1, 3),        # Bucharest and Warsaw
    (4, 0), (0, 4)         # Copenhagen and Dubrovnik
]

DAYS = 19  # Base days indexed 0..18

# Create variables:
# c[d] is the base city on day d (for d=0...18).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a boolean indicating whether a flight occurs on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's city must be one of {0,...,4}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 5)

# Day 0 always starts a new segment.
s.add(isSeg[0] == True)

# For days 1..18, define flight and segment variables.
for d in range(1, DAYS):
    # A flight is taken if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the flight route must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 4 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# The starting city of each segment must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(5):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions.
# On day 0, add 1 to the corresponding city.
# For day d (>=1):
#   if a flight occurs then count 1 for departure (c[d-1]) and 1 for arrival (c[d]),
#   otherwise count 1 for c[d] only.
counts = [Int(f"count_{city}") for city in range(5)]
for city in range(5):
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

# Helper: inCityOnDay returns a condition that the itinerary "includes" target city on day d.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    # If a flight occurs on day d, then both the departing city (c[d-1]) and arriving city (c[d]) count.
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Conference in Stuttgart (city 2) on day 7 and day 13.
#    Day 7 -> index 6; day 13 -> index 12.
s.add(inCityOnDay(6, 2))
s.add(inCityOnDay(12, 2))

# 2. Wedding in Bucharest (city 3) between day 1 and day 6 (indices 0 to 5).
wedding_condition = [inCityOnDay(d, 3) for d in range(0, 6)]
s.add(Or(wedding_condition))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_info = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_info += f" (Flight: {dep} -> {arr})"
        print(day_info)
    print("\nCity day contributions:")
    for i in range(5):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")