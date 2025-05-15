from z3 import *

# City indices and requirements:
# 0: Riga       – 4 days
# 1: Manchester – 5 days
# 2: Bucharest  – 4 days; event: attend workshop in Bucharest between day 16 and day 19.
# 3: Florence   – 4 days
# 4: Vienna     – 2 days
# 5: Istanbul   – 2 days; event: annual show in Istanbul between day 12 and day 13.
# 6: Reykjavik  – 4 days
# 7: Stuttgart  – 5 days
city_names = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
req = [4, 5, 4, 4, 2, 2, 4, 5]

# Total required day contributions = 4+5+4+4+2+2+4+5 = 30.
# Base days = 23, so extra contributions = 30 - 23 = 7.
# That implies exactly 7 flights (each flight adds an extra contribution).
# Consequently, the itinerary is partitioned into 8 segments (each visited city exactly once).

DAYS = 23  # Day indices 0..22 represent days 1..23

# Allowed direct flights (each pair is interpreted as (from, to), with bidirectionality unless noted):
# Bucharest and Vienna:         (2,4) and (4,2)
# Reykjavik and Vienna:         (6,4) and (4,6)
# Manchester and Vienna:        (1,4) and (4,1)
# Manchester and Riga:          (1,0) and (0,1)
# Riga and Vienna:              (0,4) and (4,0)
# Istanbul and Vienna:          (5,4) and (4,5)
# Vienna and Florence:          (4,3) and (3,4)
# Stuttgart and Vienna:         (7,4) and (4,7)
# Riga and Bucharest:           (0,2) and (2,0)
# Istanbul and Riga:            (5,0) and (0,5)
# Stuttgart and Istanbul:       (7,5) and (5,7)
# from Reykjavik to Stuttgart:  (6,7)   [one-way only: from Reykjavik to Stuttgart]
# Istanbul and Bucharest:       (5,2) and (2,5)
# Manchester and Istanbul:      (1,5) and (5,1)
# Manchester and Bucharest:     (1,2) and (2,1)
# Stuttgart and Manchester:     (7,1) and (1,7)
allowed_flights = [
    (2,4), (4,2),
    (6,4), (4,6),
    (1,4), (4,1),
    (1,0), (0,1),
    (0,4), (4,0),
    (5,4), (4,5),
    (4,3), (3,4),
    (7,4), (4,7),
    (0,2), (2,0),
    (5,0), (0,5),
    (7,5), (5,7),
    (6,7),  # one-way: Reykjavik -> Stuttgart only
    (5,2), (2,5),
    (1,5), (5,1),
    (1,2), (2,1),
    (7,1), (1,7)
]

# Create Z3 variables:
# c[d]: base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: True if a flight is taken on day d (for d>=1, day0 is the start of the itinerary)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: True if day d is the start of a new segment (i.e. day0 or a day when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: Each day's city is an integer in [0,7].
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is the start of a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1, determine if a flight occurs, and if so, enforce an allowed flight.
for d in range(1, DAYS):
    # Flight happens if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If there is a flight on day d, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 7 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 7)

# 5. The starting city of each segment (day0 and every day when a flight occurs) must be unique.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, force that every city is visited at least once.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0: city c[0] gets a contribution of 1.
# For each day d>=1:
#    - If a flight occurs on day d, then both c[d-1] and c[d] receive 1 contribution each.
#    - If no flight occurs, only c[d] receives 1 contribution.
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

# Helper function:
# inCityOnDay(d, target) returns a Z3 condition that asserts that on day d the itinerary includes the target city.
# On a flight day, the itinerary includes both the departure city (c[d-1]) and the arrival city (c[d]).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Bucharest workshop: attend workshop in Bucharest (city 2) between day 16 and day 19.
# Day 16 to day 19 correspond to indices 15, 16, 17, and 18.
bucharest_workshop = [inCityOnDay(d, 2) for d in range(15, 19)]
s.add(Or(bucharest_workshop))

# (b) Istanbul annual show: attend annual show in Istanbul (city 5) between day 12 and day 13.
# Day 12 and day 13 correspond to indices 11 and 12.
istanbul_show = [inCityOnDay(d, 5) for d in [11, 12]]
s.add(Or(istanbul_show))

# Solve and output the itinerary:
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_line = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_line += f" (Flight: {dep} -> {arr})"
        print(day_line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")