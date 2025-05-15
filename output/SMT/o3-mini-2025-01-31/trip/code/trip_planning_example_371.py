from z3 import *

# Cities:
# 0: Nice      – 2 days
# 1: Stockholm – 5 days
# 2: Split     – 3 days; event: attend conference in Split on day 7 and day 9.
# 3: Vienna    – 2 days; event: attend workshop in Vienna between day 1 and day 2.
city_names = ["Nice", "Stockholm", "Split", "Vienna"]
req = [2, 5, 3, 2]  # required day contributions

# Total required contributions = 2 + 5 + 3 + 2 = 12.
# Base days = 9, so extra contributions from flights = 12 - 9 = 3.
# Thus, exactly 3 flights, and the trip is partitioned into 4 segments (one per city).

DAYS = 9  # days 0..8 represent days 1..9

# Allowed flights (bidirectional):
# Vienna and Stockholm, Vienna and Nice, Vienna and Split, Stockholm and Split, Nice and Stockholm.
allowed_flights = [
    (3, 1), (1, 3),   # Vienna <-> Stockholm
    (3, 0), (0, 3),   # Vienna <-> Nice
    (3, 2), (2, 3),   # Vienna <-> Split
    (1, 2), (2, 1),   # Stockholm <-> Split
    (0, 1), (1, 0)    # Nice <-> Stockholm
]

# Create Z3 variables
# c[d]: base city on day d (0-indexed)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: True if a flight occurs on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: True if day d starts a new segment (day 0 and days with flights)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each day the city must be an integer in 0...3.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 4)

# 2. Day0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For days 1 to 8, define flight and segment indicators.
for d in range(1, DAYS):
    # A flight occurs when the city changes
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the flight must be one of the allowed direct flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Must have exactly 3 flights.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 3)

# 5. The starting city of each segment (day 0 and days with flights) should be unique,
# ensuring each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce every city appears at least once.
for city in range(4):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city:
# Day 0 contributes 1 to c[0].
# For d>=1:
#   - If flight happens on day d, add 1 for departure (c[d-1]) and 1 for arrival (c[d]).
#   - Otherwise, add 1 for the city on that day.
counts = [Int(f"count_{city}") for city in range(4)]
for city in range(4):
    base = If(c[0] == city, 1, 0)
    day_sum = []
    for d in range(1, DAYS):
        day_sum.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(day_sum))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay(d, target)
# Returns a Z3 condition asserting that on day d the itinerary "includes" the target city.
# On a flight day, both departure and arrival count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Add event constraints:
# Conference in Split (city 2) on day 7 and day 9 -> indices 6 and 8.
s.add(inCityOnDay(6, 2))
s.add(inCityOnDay(8, 2))
# Workshop in Vienna (city 3) between day 1 and day 2 -> indices 0 and 1.
s.add(Or(inCityOnDay(0, 3), inCityOnDay(1, 3)))

# Solve and output the solution:
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city = m[c[d]].as_long()
        line = f"Day {d+1:2d}: {city_names[city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city]
            line += f" (Flight: {dep} -> {arr})"
        print(line)
    print("\nCity day contributions:")
    for i in range(4):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")