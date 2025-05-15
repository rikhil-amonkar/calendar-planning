from z3 import *

# City indices and requirements:
# 0: Stuttgart  – 4 days; event: attend a conference in Stuttgart on day 4 and day 7.
# 1: Istanbul   – 4 days; event: visit relatives in Istanbul between day 19 and day 22.
# 2: Vilnius    – 4 days.
# 3: Seville    – 3 days.
# 4: Geneva     – 5 days.
# 5: Valencia   – 5 days.
# 6: Munich     – 3 days; event: annual show in Munich from day 13 to day 15.
# 7: Reykjavik  – 4 days; event: attend a workshop in Reykjavik between day 1 and day 4.
city_names = ["Stuttgart", "Istanbul", "Vilnius", "Seville", "Geneva", "Valencia", "Munich", "Reykjavik"]
req = [4, 4, 4, 3, 5, 5, 3, 4]  # Total required contributions = 32

# Base days = 25. Extra contributions come from flight days.
# Each flight day adds 1 extra credit relative to a non-flight day.
# Thus, 32 - 25 = 7 extra contributions mean exactly 7 flights.
# With 7 flights the itinerary is partitioned into 8 segments (one per city).
DAYS = 25

# Allowed direct flights.
# Unless indicated as "from X to Y", we assume bidirectional.
# Using our city indices:
#  - Geneva and Istanbul: (4,1) and (1,4)
#  - Reykjavik and Munich: (7,6) and (6,7)
#  - Stuttgart and Valencia: (0,5) and (5,0)
#  - from Reykjavik to Stuttgart: (7,0) [one-way]
#  - Stuttgart and Istanbul: (0,1) and (1,0)
#  - Munich and Geneva: (6,4) and (4,6)
#  - Istanbul and Vilnius: (1,2) and (2,1)
#  - Valencia and Seville: (5,3) and (3,5)
#  - Valencia and Istanbul: (5,1) and (1,5)
#  - from Vilnius to Munich: (2,6) [one-way]
#  - Seville and Munich: (3,6) and (6,3)
#  - Munich and Istanbul: (6,1) and (1,6)
#  - Valencia and Geneva: (5,4) and (4,5)
#  - Valencia and Munich: (5,6) and (6,5)
allowed_flights = [
    (4,1), (1,4),                           # Geneva <-> Istanbul
    (7,6), (6,7),                           # Reykjavik <-> Munich
    (0,5), (5,0),                           # Stuttgart <-> Valencia
    (7,0),                                  # from Reykjavik to Stuttgart (one-way)
    (0,1), (1,0),                           # Stuttgart <-> Istanbul
    (6,4), (4,6),                           # Munich <-> Geneva
    (1,2), (2,1),                           # Istanbul <-> Vilnius
    (5,3), (3,5),                           # Valencia <-> Seville
    (5,1), (1,5),                           # Valencia <-> Istanbul
    (2,6),                                  # from Vilnius to Munich (one-way)
    (3,6), (6,3),                           # Seville <-> Munich
    (6,1), (1,6),                           # Munich <-> Istanbul
    (5,4), (4,5),                           # Valencia <-> Geneva
    (5,6), (6,5)                            # Valencia <-> Munich
]

# Create Z3 variables.
# c[d] is the base city (the city you are "in") on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] indicates if there is a flight on day d (for d>=1; day 0 is simply the starting city)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d marks the start of a new segment (day 0 or when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each day's base city is an integer between 0 and 7, inclusive.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1, determine flight occurrence and enforce allowed flight transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if there is a change in the base city from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 7 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 7)

# 5. The starting base cities of each segment (day 0 and any day when a flight occurs)
# must all be distinct. This ensures that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, ensure that every city is visited at least once.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Calculate the day contributions for each city.
# Day 0 contributes 1 to the city c[0].
# For each day d>=1:
#   - If a flight occurs on day d, then both the previous city (departure) and the current city (arrival)
#     get 1 credit.
#   - If no flight occurs, then only the current city's credit increases by 1.
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

# Helper function: on day d, the itinerary "includes" a target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Conference in Stuttgart (city 0) on day 4 and day 7.
s.add(inCityOnDay(3, 0))  # Day 4
s.add(inCityOnDay(6, 0))  # Day 7

# (b) Relatives in Istanbul (city 1) between day 19 and day 22: days indices 18 to 21.
istanbul_event = [inCityOnDay(d, 1) for d in range(18, 22)]
s.add(Or(istanbul_event))

# (c) Annual show in Munich (city 6) from day 13 to day 15: indices 12, 13, 14.
munich_event = [inCityOnDay(d, 6) for d in range(12, 15)]
s.add(Or(munich_event))

# (d) Workshop in Reykjavik (city 7) between day 1 and day 4: indices 0 to 3.
reykjavik_event = [inCityOnDay(d, 7) for d in range(0, 4)]
s.add(Or(reykjavik_event))

# Solve the model and print the itinerary.
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