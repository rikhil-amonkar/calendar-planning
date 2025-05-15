from z3 import *

# Cities (indices) and requirements:
# 0: Stuttgart – 3 days; event: attend workshop in Stuttgart between day 11 and day 13.
# 1: Edinburgh – 4 days.
# 2: Athens    – 4 days.
# 3: Split     – 2 days; event: meet friends at Split between day 13 and day 14.
# 4: Krakow    – 4 days; event: meet a friend in Krakow between day 8 and day 11.
# 5: Venice    – 5 days.
# 6: Mykonos   – 4 days.
city_names = ["Stuttgart", "Edinburgh", "Athens", "Split", "Krakow", "Venice", "Mykonos"]
req = [3, 4, 4, 2, 4, 5, 4]   # required day contributions

# Total required contributions = 3+4+4+2+4+5+4 = 26.
# Base days = 20. The extra contributions needed come from flights.
# 26 - 20 = 6; so exactly 6 flights are required.
# That splits the itinerary into 7 segments (each segment being a visit to one city).

DAYS = 20  # day indices: 0 .. 19 correspond to days 1..20

# Allowed direct flights (each pair is bidirectional unless noted otherwise):
# Krakow and Split         -> (4,3) and (3,4)
# Split and Athens         -> (3,2) and (2,3)
# Edinburgh and Krakow     -> (1,4) and (4,1)
# Venice and Stuttgart     -> (5,0) and (0,5)
# Krakow and Stuttgart     -> (4,0) and (0,4)
# Edinburgh and Stuttgart  -> (1,0) and (0,1)
# Stuttgart and Athens     -> (0,2) and (2,0)
# Venice and Edinburgh     -> (5,1) and (1,5)
# Athens and Mykonos       -> (2,6) and (6,2)
# Venice and Athens        -> (5,2) and (2,5)
# Stuttgart and Split      -> (0,3) and (3,0)
# Edinburgh and Athens     -> (1,2) and (2,1)
allowed_flights = [
    (4,3), (3,4),
    (3,2), (2,3),
    (1,4), (4,1),
    (5,0), (0,5),
    (4,0), (0,4),
    (1,0), (0,1),
    (0,2), (2,0),
    (5,1), (1,5),
    (2,6), (6,2),
    (5,2), (2,5),
    (0,3), (3,0),
    (1,2), (2,1)
]

# Create Z3 variables:
# c[d]: base city on day d (0 <= d < DAYS)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: indicates if a flight occurs on day d (for d>=1; day 0 is start of itinerary)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: indicates if day d starts a new segment (either day 0 or a flight day)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraint: each day's city index is between 0 and 6.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 starts a segment.
s.add(isSeg[0] == True)

# 3. For each day from 1 to DAYS-1, determine if a flight occurs and enforce allowed flight constraints.
for d in range(1, DAYS):
    # Flight happens if and only if the city changes compared to the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the pair (c[d-1], c[d]) must be one of the allowed direct flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 6 flights are required.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# 5. The starting cities of each segment (day 0 and flight days) must be unique (each city is visited once).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city appears at least once.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# The model: Day 0 contributes 1 for c[0].
# For each subsequent day d:
#   - If a flight occurs on day d, then add 1 for departure (c[d-1]) and 1 for arrival (c[d]).
#   - If no flight occurs, add 1 for the city on day d.
counts = [Int(f"count_{city}") for city in range(len(city_names))]
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

# Helper function: inCityOnDay(d, target)
# This returns a condition asserting that on day d, the itinerary "includes" the target city.
# On a flight day, either the departure (c[d-1]) or arrival (c[d]) qualifies.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Attend workshop in Stuttgart (city 0) between day 11 and day 13.
# Days 11, 12, 13 correspond to indices 10, 11, and 12.
stuttgart_workshop = [inCityOnDay(d, 0) for d in range(10, 13)]
s.add(Or(stuttgart_workshop))

# (b) Meet a friend in Krakow (city 4) between day 8 and day 11.
# Days 8, 9, 10, 11 correspond to indices 7, 8, 9, and 10.
krakow_meet = [inCityOnDay(d, 4) for d in range(7, 11)]
s.add(Or(krakow_meet))

# (c) Meet friends at Split (city 3) between day 13 and day 14.
# Days 13 and 14 correspond to indices 12 and 13.
split_meet = [inCityOnDay(d, 3) for d in [12, 13]]
s.add(Or(split_meet))

# Solve and print the itinerary:
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        ci = m[c[d]].as_long()
        line = f"Day {d+1:2d}: {city_names[ci]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[ci]
            line += f" (Flight: {dep} -> {arr})"
        print(line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")