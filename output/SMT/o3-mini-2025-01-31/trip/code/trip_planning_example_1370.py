from z3 import *

# City indices and names:
# 0: Santorini   (5 days; event: meet friend between day 25 and 29)
# 1: Krakow      (5 days; event: wedding between day 18 and 22)
# 2: Paris       (5 days; event: meet friend between day 11 and 15)
# 3: Vilnius     (3 days)
# 4: Munich      (5 days)
# 5: Geneva      (2 days)
# 6: Amsterdam   (4 days)
# 7: Budapest    (5 days)
# 8: Split       (4 days)
city_names = ["Santorini", "Krakow", "Paris", "Vilnius", "Munich", "Geneva", "Amsterdam", "Budapest", "Split"]

# Required day counts.
req = [5, 5, 5, 3, 5, 2, 4, 5, 4]

# Total sum of required days = 5+5+5+3+5+2+4+5+4 = 38.
# Total base days = 30. Since each flight day contributes an extra day,
# we require f flights with 30 + f = 38, hence f = 8.
# This also means we have 9 segments (start days of segments are distinct),
# each corresponding to one of the 9 cities.

# Allowed direct flights.
# For bidirectional connections, both orders are allowed.
allowed_flights = [
    # Paris and Krakow
    (2, 1), (1, 2),
    # Paris and Amsterdam
    (2, 6), (6, 2),
    # Paris and Split
    (2, 8), (8, 2),
    # from Vilnius to Munich (only this direction)
    (3, 4),
    # Paris and Geneva
    (2, 5), (5, 2),
    # Amsterdam and Geneva
    (6, 5), (5, 6),
    # Munich and Split
    (4, 8), (8, 4),
    # Split and Krakow
    (8, 1), (1, 8),
    # Munich and Amsterdam
    (4, 6), (6, 4),
    # Budapest and Amsterdam
    (7, 6), (6, 7),
    # Split and Geneva
    (8, 5), (5, 8),
    # Vilnius and Split
    (3, 8), (8, 3),
    # Munich and Geneva
    (4, 5), (5, 4),
    # Munich and Krakow
    (4, 1), (1, 4),
    # from Krakow to Vilnius (only this direction)
    (1, 3),
    # Vilnius and Amsterdam
    (3, 6), (6, 3),
    # Budapest and Paris
    (7, 2), (2, 7),
    # Krakow and Amsterdam
    (1, 6), (6, 1),
    # Vilnius and Paris
    (3, 2), (2, 3),
    # Budapest and Geneva
    (7, 5), (5, 7),
    # Split and Amsterdam
    (8, 6), (6, 8),
    # Santorini and Geneva
    (0, 5), (5, 0),
    # Amsterdam and Santorini
    (6, 0), (0, 6),
    # Munich and Budapest
    (4, 7), (7, 4),
    # Munich and Paris
    (4, 2), (2, 4)
]

# Total itinerary days.
DAYS = 30

# Create Z3 variables:
# c[d] is the base city on day d (0-indexed, representing day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean for day d (for d>=1) indicating that a flight occurs on that day
# (i.e. the base city changes from the previous day).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a segment (day 0 always, and every day when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be one of the 9 cities.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 9))

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# Define flight indicators and allowed flights on days 1..DAYS-1.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If there is a flight, then (c[d-1], c[d]) must be one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 8 flights are required.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 8)

# Ensure that the cities at the start of each segment (day 0 and every flight day) are distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, require that each city appears at least once.
for city in range(9):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contribution" for each city:
# On day 0, the traveler is in city c[0] (contributes 1).
# For each day d (1 <= d < DAYS):
#   If a flight occurs on day d, both the departure (c[d-1]) and the arrival (c[d]) get 1 each.
#   Otherwise, only c[d] gets 1.
counts = [Int(f"count_{city}") for city in range(9)]
for city in range(9):
    base = If(c[0] == city, 1, 0)
    contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        contribs.append(contrib)
    s.add(counts[city] == base + Sum(contribs))
    s.add(counts[city] == req[city])

# Helper: inCityOnDay returns a constraint ensuring that on day d the trip "includes" target city.
# On day 0, it means c[0] == target.
# For d >= 1: if a flight occurs, then the traveler is in both c[d-1] and c[d], else only c[d].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints (event constraints):
# 1. Meet your friends at Santorini (city 0) between day 25 and day 29 (indices 24 to 28).
friend_santorini = [inCityOnDay(d, 0) for d in range(24, 29)]
s.add(Or(friend_santorini))

# 2. Attend the wedding in Krakow (city 1) between day 18 and day 22 (indices 17 to 21).
wedding_krakow = [inCityOnDay(d, 1) for d in range(17, 22)]
s.add(Or(wedding_krakow))

# 3. Meet a friend in Paris (city 2) between day 11 and day 15 (indices 10 to 14).
friend_paris = [inCityOnDay(d, 2) for d in range(10, 15)]
s.add(Or(friend_paris))

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
    for city in range(9):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")