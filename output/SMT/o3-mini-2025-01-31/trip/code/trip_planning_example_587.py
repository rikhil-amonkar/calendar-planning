from z3 import *

# City indices and names:
# 0: Manchester  (3 days; event: wedding in Manchester between day 1 and day 3)
# 1: Istanbul    (7 days)
# 2: Venice      (7 days; event: workshop in Venice between day 3 and day 9)
# 3: Krakow      (6 days)
# 4: Lyon        (2 days)
city_names = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]

# Required day counts.
req = [3, 7, 7, 6, 2]

# Total required contributions = 3 + 7 + 7 + 6 + 2 = 25.
# We have 21 base days, so the extra flight contributions must add up to 4, i.e. there must be 4 flight days.
# This yields 5 segments (each corresponding to one city) which must all be distinct.

# Allowed direct flights (bidirectional):
allowed_flights = [
    # Manchester and Venice
    (0, 2), (2, 0),
    # Manchester and Istanbul
    (0, 1), (1, 0),
    # Venice and Istanbul
    (2, 1), (1, 2),
    # Istanbul and Krakow
    (1, 3), (3, 1),
    # Venice and Lyon
    (2, 4), (4, 2),
    # Lyon and Istanbul
    (4, 1), (1, 4),
    # Manchester and Krakow
    (0, 3), (3, 0)
]

# Total number of itinerary days.
DAYS = 21

# Create Z3 variables.
# c[d] represents the "base city" on day d (for day d+1) such that c[d] is in {0,...,4}.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable (for d>=1) indicating that on day d a flight occurs.
# If flight[d] is True then c[d] != c[d-1] and the traveler is counted as visiting both c[d-1] and c[d] on day d.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates that day d is the start of a segment (day 0 always, and every day with a flight).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be between 0 and 4.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 5))

# Day 0 is the start of a segment.
s.add(isSeg[0] == True)

# For days 1 to 20, define flight indicators.
for d in range(1, DAYS):
    # A flight occurs on day d if and only if c[d] != c[d-1].
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, then (c[d-1], c[d]) must be an allowed direct flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 4 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# The starting city of each segment (day 0 and every day that is a flight day) must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally ensure that each city is visited at least once.
for city in range(5):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions:
# On day 0, the traveler contributes 1 for city c[0].
# For each day d from 1 to 20:
#   - If flight[d] occurs, then that day contributes 1 to c[d-1] (departure) and 1 to c[d] (arrival).
#   - If no flight occurs, then day d contributes 1 to c[d].
counts = [Int(f"count_{city}") for city in range(5)]
for city in range(5):
    base = If(c[0] == city, 1, 0)
    day_contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        day_contribs.append(contrib)
    s.add(counts[city] == base + Sum(day_contribs))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay returns a constraint that on day d the itinerary "includes" the target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints for events:
# 1. Wedding in Manchester (city 0) between day 1 and day 3 (indices 0,1,2).
wedding_manchester = [inCityOnDay(d, 0) for d in range(0, 3)]
s.add(Or(wedding_manchester))

# 2. Workshop in Venice (city 2) between day 3 and day 9 (indices 2 through 8).
workshop_venice = [inCityOnDay(d, 2) for d in range(2, 9)]
s.add(Or(workshop_venice))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city = city_names[m[c[d]].as_long()]
        day_str = f"Day {d+1:2d}: In {city}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for city in range(5):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")