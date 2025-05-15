from z3 import *

# City indices and names:
# 0: Venice      (3 days)
# 1: Reykjavik   (2 days)
# 2: Munich      (3 days; event: annual show in Munich between day 4 and day 6)
# 3: Santorini   (3 days; event: visit relatives in Santorini between day 8 and day 10)
# 4: Manchester  (3 days)
# 5: Porto       (3 days)
# 6: Bucharest   (5 days)
# 7: Tallinn     (4 days)
# 8: Valencia    (2 days; event: attend workshop in Valencia between day 14 and day 15)
# 9: Vienna      (5 days)
city_names = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]

# Required day counts for each city:
req = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]

# Total required day contributions = sum(req) = 3+2+3+3+3+3+5+4+2+5 = 33.
# There are 24 base days and extra contribution on flight days: total contributions = 24 + (# flights).
# So we require 24 + f = 33, hence f = 9 flights.
# That gives us 10 segments corresponding to the 10 distinct cities.

# Allowed direct flights (bidirectional):
allowed_flights = [
    # Bucharest and Manchester
    (6, 4), (4, 6),
    # Munich and Venice
    (2, 0), (0, 2),
    # Santorini and Manchester
    (3, 4), (4, 3),
    # Vienna and Reykjavik
    (9, 1), (1, 9),
    # Venice and Santorini
    (0, 3), (3, 0),
    # Munich and Porto
    (2, 5), (5, 2),
    # Valencia and Vienna
    (8, 9), (9, 8),
    # Manchester and Vienna
    (4, 9), (9, 4),
    # Porto and Vienna
    (5, 9), (9, 5),
    # Venice and Manchester
    (0, 4), (4, 0),
    # Santorini and Vienna
    (3, 9), (9, 3),
    # Munich and Manchester
    (2, 4), (4, 2),
    # Munich and Reykjavik
    (2, 1), (1, 2),
    # Bucharest and Valencia
    (6, 8), (8, 6),
    # Venice and Vienna
    (0, 9), (9, 0),
    # Bucharest and Vienna
    (6, 9), (9, 6),
    # Porto and Manchester
    (5, 4), (4, 5),
    # Munich and Vienna
    (2, 9), (9, 2),
    # Valencia and Porto
    (8, 5), (5, 8),
    # Munich and Bucharest
    (2, 6), (6, 2),
    # Tallinn and Munich
    (7, 2), (2, 7),
    # Santorini and Bucharest
    (3, 6), (6, 3),
    # Munich and Valencia
    (2, 8), (8, 2)
]

# Total itinerary days.
DAYS = 24

# Create Z3 variables:
# c[d] is the "base city" on day d (for day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable (defined for days d >= 1) indicating a flight occurs on day d.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (either day 0 or a flight day).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be one of the 10 cities.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 10))

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight indicators and enforce allowed flight constraints.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then (c[d-1], c[d]) must be one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 9 flights occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# The cities at the start of each segment (day 0 and every flight day) must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, ensure that each city is visited at least once.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contributions" for each city:
# On day 0, the traveler contributes 1 in the base city c[0].
# For each day d >= 1:
#   If a flight occurs on day d, add 1 for c[d-1] (departure) and 1 for c[d] (arrival).
#   Otherwise, add 1 for c[d].
counts = [Int(f"count_{city}") for city in range(10)]
for city in range(10):
    base = If(c[0] == city, 1, 0)
    daily_contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        daily_contribs.append(contrib)
    s.add(counts[city] == base + Sum(daily_contribs))
    s.add(counts[city] == req[city])

# Helper: inCityOnDay returns a constraint that on day d the traveler "includes" the target city.
def inCityOnDay(d, target):
    # On day 0, simply c[0] == target.
    if d == 0:
        return c[0] == target
    # For d>=1, if a flight occurs, the traveler is in both c[d-1] and c[d].
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional event constraints:
# 1. Annual show in Munich (city 2) between day 4 and day 6 (days 4,5,6 -> indices 3,4,5).
show_munich = [inCityOnDay(d, 2) for d in range(3, 6)]
s.add(Or(show_munich))

# 2. Visit relatives in Santorini (city 3) between day 8 and day 10 (indices 7,8,9).
relatives_santorini = [inCityOnDay(d, 3) for d in range(7, 10)]
s.add(Or(relatives_santorini))

# 3. Attend workshop in Valencia (city 8) between day 14 and day 15 (indices 13,14).
workshop_valencia = [inCityOnDay(d, 8) for d in [13, 14]]
s.add(Or(workshop_valencia))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        day_str = f"Day {d+1:2d}: In {city_names[m[c[d]].as_long()]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[m[c[d]].as_long()]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for city in range(10):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")