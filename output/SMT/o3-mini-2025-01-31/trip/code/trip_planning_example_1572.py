from z3 import *

# City indices and names:
# 0: Lyon      (3 days)
# 1: Paris     (5 days)
# 2: Riga      (2 days)
# 3: Berlin    (2 days; event: wedding in Berlin between day 1 and day 2)
# 4: Stockholm (3 days; event: annual show in Stockholm from day 20 to day 22)
# 5: Zurich    (5 days)
# 6: Nice      (2 days; event: workshop in Nice between day 12 and day 13)
# 7: Seville   (3 days)
# 8: Milan     (3 days)
# 9: Naples    (4 days)
city_names = ["Lyon", "Paris", "Riga", "Berlin", "Stockholm", "Zurich", "Nice", "Seville", "Milan", "Naples"]

# Required day contributions per city.
req = [3, 5, 2, 2, 3, 5, 2, 3, 3, 4]
# Total contributions = sum(req) = 3+5+2+2+3+5+2+3+3+4 = 32.
# Base days = 23.
# Each flight day (when a flight occurs) adds an extra count (departure and arrival both count)
# Thus we have: 23 + (#flights) = 32.
# So we must have exactly 9 flights.
#
# With 9 flights the trip is split into 10 segments. We force the starting city
# of each segment (day 0 and any day with a flight) to be distinct so every city is visited.

# Allowed direct flights (bidirectional unless noted otherwise):
allowed_flights = [
    # Paris and Stockholm
    (1, 4), (4, 1),
    # Seville and Paris
    (7, 1), (1, 7),
    # Naples and Zurich
    (9, 5), (5, 9),
    # Nice and Riga
    (6, 2), (2, 6),
    # Berlin and Milan
    (3, 8), (8, 3),
    # Paris and Zurich
    (1, 5), (5, 1),
    # Paris and Nice
    (1, 6), (6, 1),
    # Milan and Paris (same as above, symmetric)
    (8, 1), (1, 8),
    # Milan and Riga
    (8, 2), (2, 8),
    # Paris and Lyon
    (1, 0), (0, 1),
    # Milan and Naples
    (8, 9), (9, 8),
    # Paris and Riga
    (1, 2), (2, 1),
    # Berlin and Stockholm
    (3, 4), (4, 3),
    # Stockholm and Riga
    (4, 2), (2, 4),
    # Nice and Zurich
    (6, 5), (5, 6),
    # Milan and Zurich
    (8, 5), (5, 8),
    # Lyon and Nice
    (0, 6), (6, 0),
    # Zurich and Stockholm
    (5, 4), (4, 5),
    # Zurich and Riga
    (5, 2), (2, 5),
    # Berlin and Naples
    (3, 9), (9, 3),
    # Milan and Stockholm
    (8, 4), (4, 8),
    # Berlin and Zurich
    (3, 5), (5, 3),
    # Milan and Seville
    (8, 7), (7, 8),
    # Paris and Naples
    (1, 9), (9, 1),
    # Berlin and Riga
    (3, 2), (2, 3),
    # Nice and Stockholm
    (6, 4), (4, 6),
    # Berlin and Paris
    (3, 1), (1, 3),
    # Nice and Naples
    (6, 9), (9, 6),
    # Berlin and Nice
    (3, 6), (6, 3)
]

# Total number of base days in the itinerary.
DAYS = 23

# Create Z3 variables.
# c[d] is the base city on day d (0-indexed, where day d corresponds to day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable indicating whether a flight occurs on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is true if day d is the start of a segment (day 0 always, and when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Constrain each day’s base city to be a valid city (0 <= city < 10).
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 10)

# Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# For days 1 to 22, define the flight indicator and segment flag.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If there is a flight on day d, then (c[d-1], c[d]) must be an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 9 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# The starting city of each segment (day 0 or any day d with flight[d] true) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally ensure each city is visited at least once.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# On day 0, add 1 for city c[0].
# For each day d = 1 ... DAYS-1:
#   if a flight occurs on day d, add 1 for the departure city (c[d-1]) and 1 for the arrival city (c[d]);
#   otherwise add 1 for city c[d].
counts = [Int(f"count_{i}") for i in range(10)]
for i in range(10):
    initial = If(c[0] == i, 1, 0)
    day_sum = []
    for d in range(1, DAYS):
        day_sum.append(
            If(flight[d],
               (If(c[d-1] == i, 1, 0) + If(c[d] == i, 1, 0)),
               If(c[d] == i, 1, 0)
            )
        )
    s.add(counts[i] == initial + Sum(day_sum))
    s.add(counts[i] == req[i])

# Helper function: inCityOnDay(d, target) returns a constraint that day d "includes" the target city.
# If a flight occurs on day d then that day counts for both the departure (d-1) and the arrival (d).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:
# 1. Wedding in Berlin (city 3) between day 1 and day 2.
# Days 1 and 2 correspond to indices 0 and 1.
wedding_berlin = [inCityOnDay(d, 3) for d in [0, 1]]
s.add(Or(wedding_berlin))

# 2. Annual show in Stockholm (city 4) from day 20 to day 22.
# That is, on at least one day among day 20, 21, 22, i.e. indices 19, 20, 21.
stockholm_show = [inCityOnDay(d, 4) for d in [19, 20, 21]]
s.add(Or(stockholm_show))

# 3. Workshop in Nice (city 6) between day 12 and day 13.
# That is, on at least one day among day 12 and day 13 (indices 11 and 12).
workshop_nice = [inCityOnDay(d, 6) for d in [11, 12]]
s.add(Or(workshop_nice))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base_city = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: In {city_names[base_city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep_city = city_names[m[c[d-1]].as_long()]
            arr_city = city_names[base_city]
            day_str += f" (Flight: {dep_city} -> {arr_city})"
        print(day_str)
    print("\nCity day counts:")
    for i in range(10):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")