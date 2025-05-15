from z3 import *

# City indices and names:
# 0: Vilnius    (7 days)
# 1: Naples     (5 days; event: visit relatives in Naples between day 1 and day 5)
# 2: Vienna     (7 days)
city_names = ["Vilnius", "Naples", "Vienna"]

# Required day counts for each city.
req = [7, 5, 7]

# Total required day contributions = 7 + 5 + 7 = 19.
# We have 17 base days; with extra contribution from flight days:
# Total contributions = 17 + (# flights)
# We need 17 + f = 19, hence f = 2 flights.
# This means the trip is divided into 3 segments, each corresponding to a distinct city.

# Allowed direct flights (bidirectional):
# Provided: Naples and Vienna, Vienna and Vilnius.
allowed_flights = [
    (1, 2), (2, 1),  # Naples <-> Vienna
    (2, 0), (0, 2)   # Vienna <-> Vilnius
]

# Total itinerary days.
DAYS = 17

# Create Z3 variables.
# c[d] represents the “base city” on day d (for day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean for day d (for d >= 1) that indicates a flight occurs on day d.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (either day 0 or a flight day).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city is in {0,1,2}.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 3))

# Day 0 starts a segment.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight indicators and enforce allowed flight constraints.
for d in range(1, DAYS):
    # A flight occurs on day d if c[d] is different from c[d-1].
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then the change of cities must be along an allowed direct flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly 2 flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# The cities at the beginning of each segment (day 0 and every day with a flight) must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, ensure that each city appears at least once.
for city in range(3):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute "day contributions" for each city. On day 0, the traveler is in c[0].
# For day d>=1:
#  - If flight occurs on day d, then add 1 for c[d-1] (departure) and 1 for c[d] (arrival).
#  - Otherwise, add 1 only for c[d].
counts = [Int(f"count_{city}") for city in range(3)]
for city in range(3):
    initial = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(If(flight[d],
                        If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                        If(c[d] == city, 1, 0)))
    s.add(counts[city] == initial + Sum(daily))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay(d, target) returns a condition that on day d the trip "includes" the target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraint: Visit relatives in Naples between day 1 and day 5.
# That is, at least one day among days 1 to 5 (indices 0 to 4) must include Naples (city index 1).
relative_naples = [inCityOnDay(d, 1) for d in range(0, 5)]
s.add(Or(relative_naples))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base_city = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: In {city_names[base_city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base_city]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for city in range(3):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")