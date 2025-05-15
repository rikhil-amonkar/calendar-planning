from z3 import *

# Cities (indices):
# 0: Frankfurt – 3 days
# 1: Naples   – 4 days
# 2: Helsinki – 4 days; event: annual show in Helsinki from day 2 to day 5.
# 3: Lyon     – 3 days
# 4: Prague   – 2 days; event: workshop in Prague between day 1 and day 2.
city_names = ["Frankfurt", "Naples", "Helsinki", "Lyon", "Prague"]
req = [3, 4, 4, 3, 2]  # required day contributions

# Total required contributions = 3 + 4 + 4 + 3 + 2 = 16.
# Base days = 12 -> extra contributions from flights = 16 - 12 = 4 flights.
# That splits the itinerary into 5 segments (each segment is a visit to one city).

DAYS = 12  # day indices 0 ... 11 represent days 1 .. 12

# Allowed direct flights (bidirectional, unless noted otherwise):
# Prague and Lyon:        (4,3) and (3,4)
# Prague and Frankfurt:   (4,0) and (0,4)
# Frankfurt and Lyon:     (0,3) and (3,0)
# Helsinki and Naples:    (2,1) and (1,2)
# Helsinki and Frankfurt: (2,0) and (0,2)
# Naples and Frankfurt:   (1,0) and (0,1)
# Prague and Helsinki:    (4,2) and (2,4)
allowed_flights = [
    (4,3), (3,4),
    (4,0), (0,4),
    (0,3), (3,0),
    (2,1), (1,2),
    (2,0), (0,2),
    (1,0), (0,1),
    (4,2), (2,4)
]

# Create Z3 variables:
# c[d] is the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (either day 0, or a flight day)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Each day's city is in {0,1,2,3,4}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For each day d>=1, determine if a flight occurs.
for d in range(1, DAYS):
    # A flight occurs if the city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight happens, ensure the flight (from c[d-1] to c[d]) is allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 4 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# 5. The starting city for each segment (day0 and flight days) must be unique.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally force that every city is visited at least once.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions.
# Day 0 counts for 1 day for city c[0].
# For each day d>=1:
#   - If there's a flight then both c[d-1] and c[d] get a day each.
#   - Else, only c[d] gets a day.
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
# Returns a condition that day d "includes" being in target city.
# On a flight day, either departing (c[d-1]) or arriving (c[d]) qualifies.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Annual show in Helsinki (city 2) from day 2 to day 5 -> indices 1 to 4.
helsinki_show = [inCityOnDay(d, 2) for d in range(1, 5)]
s.add(Or(helsinki_show))

# (b) Workshop in Prague (city 4) between day 1 and day 2 -> indices 0 and 1.
prague_workshop = [inCityOnDay(d, 4) for d in [0, 1]]
s.add(Or(prague_workshop))

# Solve and print itinerary.
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
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")