from z3 import *

# We have 3 European cities:
# 0: Vilnius    (4 days)
# 1: Munich     (3 days)
# 2: Mykonos    (7 days)
city_names = ["Vilnius", "Munich", "Mykonos"]
req = [4, 3, 7]  # Required day contributions for each city

# Total required contributions = 4 + 3 + 7 = 14.
# We plan to have 12 base days. A flight day contributes an extra day because it counts for both
# the departure and arrival cities. Hence:
#      12 + (#flights) = 14  ->  #flights must be 2.
# With 2 flights the trip is split into 3 segments (each corresponding to one visited city).

# Allowed direct flights:
# "from Vilnius to Munich" is allowed (directional from city 0 to city 1).
# "Munich and Mykonos" are connected bidirectionally, so both (1,2) and (2,1) are allowed.
allowed_flights = [
    (0, 1),          # Vilnius -> Munich
    (1, 2), (2, 1)   # Munich <-> Mykonos
]

DAYS = 12  # We have 12 base days, indexed 0..11

# Create Z3 variables:
# c[d] is an integer variable representing the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable indicating if a flight occurs on day d (for d >= 1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each day's base city must be one of 0, 1, or 2.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 3))

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. For days 1 to DAYS-1, determine if a flight occurs.
for d in range(1, DAYS):
    # A flight is taken on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # Mark day d as a new segment start if a flight occurs.
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, the pair (c[d-1], c[d]) must be one of the allowed flights.
    allowed_conditions = [And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights]
    s.add(Implies(flight[d], Or(allowed_conditions)))

# 4. There must be exactly 2 flights among days 1..11.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# 5. Enforce that the start of each segment (i.e. each time we take a flight + day0) must be 
#    in distinct cities (so that each city is visited exactly once).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that each city is visited at least once.
for city in range(3):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute the day contributions for each city.
#    - On day 0, the city c[0] gets 1.
#    - For each day d>=1:
#         if a flight occurs on day d, then both the departure city (c[d-1]) and arrival city (c[d])
#         get a contribution of 1.
#         Otherwise, if no flight occurs, only the city's c[d] day gets a contribution of 1.
counts = [Int(f"count_{city}") for city in range(3)]
for city in range(3):
    # Day 0
    init = If(c[0] == city, 1, 0)
    daily_contrib = []
    for d in range(1, DAYS):
        # Add contributions based on flight status at day d.
        daily_contrib.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(daily_contrib))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay(d, target)
# This returns a condition that on day d the itinerary "includes" the target city.
# If a flight occurs on day d, then both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# There are no additional event constraints in this problem.

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(3):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")