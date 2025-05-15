from z3 import *

# City indices and requirements:
# 0: Stockholm  – 3 days
# 1: Hamburg    – 5 days
# 2: Florence   – 2 days
# 3: Istanbul   – 5 days, with an annual show between day 25 and day 29
# 4: Oslo       – 5 days
# 5: Vilnius    – 5 days
# 6: Santorini  – 2 days
# 7: Munich     – 5 days
# 8: Frankfurt  – 4 days
# 9: Krakow     – 5 days, with a workshop between day 5 and day 9
city_names = ["Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo", "Vilnius", "Santorini", "Munich", "Frankfurt", "Krakow"]
req = [3, 5, 2, 5, 5, 5, 2, 5, 4, 5]
# Total required day contributions = 41.
# Base days = 32, so extra contribution (from flight days) = 41 - 32 = 9.
# Hence exactly 9 flights must occur, partitioning the itinerary into 10 segments (each city visited once).

DAYS = 32  # Days indexed 0 .. 31 representing days 1..32

# Allowed direct flights.
# Note: unless noted with "from", flights are bidirectional.
allowed_flights = [
    # Oslo and Stockholm
    (4,0), (0,4),
    # Krakow and Frankfurt
    (9,8), (8,9),
    # Krakow and Istanbul
    (9,3), (3,9),
    # Munich and Stockholm
    (7,0), (0,7),
    # Hamburg and Stockholm
    (1,0), (0,1),
    # from Krakow to Vilnius (one-way)
    (9,5),
    # Oslo and Istanbul
    (4,3), (3,4),
    # Istanbul and Stockholm
    (3,0), (0,3),
    # Oslo and Krakow
    (4,9), (9,4),
    # Vilnius and Istanbul
    (5,3), (3,5),
    # Oslo and Vilnius
    (4,5), (5,4),
    # Frankfurt and Istanbul
    (8,3), (3,8),
    # Oslo and Frankfurt
    (4,8), (8,4),
    # Munich and Hamburg
    (7,1), (1,7),
    # Munich and Istanbul
    (7,3), (3,7),
    # Oslo and Munich
    (4,7), (7,4),
    # Frankfurt and Florence
    (8,2), (2,8),
    # Oslo and Hamburg
    (4,1), (1,4),
    # Vilnius and Frankfurt
    (5,8), (8,5),
    # from Florence to Munich (one-way)
    (2,7),
    # Krakow and Munich
    (9,7), (7,9),
    # Hamburg and Istanbul
    (1,3), (3,1),
    # Frankfurt and Stockholm
    (8,0), (0,8),
    # from Stockholm to Santorini (one-way)
    (0,6),
    # Frankfurt and Munich
    (8,7), (7,8),
    # from Santorini to Oslo (one-way)
    (6,4),
    # Krakow and Stockholm
    (9,0), (0,9),
    # from Vilnius to Munich (one-way)
    (5,7),
    # Frankfurt and Hamburg
    (8,1), (1,8)
]

# Create Z3 variables:
# c[d] is the "base" city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (d >= 1; day 0 is simply the start city)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (i.e. day 0 or when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Ensure each day's base city is one of the available cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is automatically a segment start.
s.add(isSeg[0] == True)

# 3. For each day d>=1, make flight[d] true if the base city changes,
# and if there is a flight then enforce that the transition (c[d-1], c[d]) is allowed.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Enforce exactly 9 flights.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# 5. The starting base cities for each segment (day 0 and those days with a flight) must be distinct,
# ensuring that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute the day contributions (the “credit”) for each city.
# On day 0, add 1 for city c[0].
# For each day d>=1, if a flight occurs then both the previous (departure) and current (arrival)
# cities get 1 credit; otherwise, only the current city gets 1 credit.
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily))
    s.add(counts[city] == req[city])

# Helper function: given day d and a target city, returns a condition stating that
# on day d the itinerary "includes" that city (both departure and arrival, if a flight occurs).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Annual show in Istanbul (city 3) between day 25 and day 29 (indices 24 to 28)
istanbul_event = [inCityOnDay(d, 3) for d in range(24, 29)]
s.add(Or(istanbul_event))

# (b) Workshop in Krakow (city 9) between day 5 and day 9 (indices 4 to 8)
krakow_event = [inCityOnDay(d, 9) for d in range(4, 9)]
s.add(Or(krakow_event))

# Solve and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        info = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            info += f" (Flight: {dep} -> {arr})"
        print(info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")