from z3 import *

# Cities (indices) and requirements:
# 0: Prague    – 4 days
# 1: Stuttgart – 2 days; event: wedding in Stuttgart between day 2 and day 3.
# 2: Split     – 2 days; event: meet friends at Split between day 3 and day 4.
# 3: Krakow    – 2 days
# 4: Florence  – 2 days
city_names = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
req = [4, 2, 2, 2, 2]  # required day contributions

# Total required contributions = 4 + 2 + 2 + 2 + 2 = 12.
# Base days = 8. Extra contributions come from flights: 12 - 8 = 4 extra.
# That means exactly 4 flights are required, partitioning the itinerary into 5 segments.

DAYS = 8  # indices 0 to 7 representing days 1 to 8

# Allowed direct flights (bidirectional):
# Stuttgart and Split     -> (1,2) and (2,1)
# Prague and Florence     -> (0,4) and (4,0)
# Krakow and Stuttgart    -> (3,1) and (1,3)
# Krakow and Split        -> (3,2) and (2,3)
# Split and Prague        -> (2,0) and (0,2)
# Krakow and Prague       -> (3,0) and (0,3)
allowed_flights = [
    (1,2), (2,1),
    (0,4), (4,0),
    (3,1), (1,3),
    (3,2), (2,3),
    (2,0), (0,2),
    (3,0), (0,3)
]

# Create Z3 variables:
# c[d] : base city on day d
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] : True if a flight occurs on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] : True if day d is the start of a new segment (either day 0 or a flight day)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each c[d] in {0,...,4}
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is a segment start.
s.add(isSeg[0] == True)

# 3. Define flight indicator for days 1..7.
for d in range(1, DAYS):
    # A flight occurs if the city changes compared to the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, ensure that the flight (c[d-1] -> c[d]) is allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 4 flights are required.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# 5. Starting cities of each segment (day0 and all flight days) must be unique (each city is visited exactly once).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that every city is visited at least once.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 contributes 1 to city c[0].
# For day d>=1:
#   - If a flight occurs, add 1 for the departure (c[d-1]) and 1 for the arrival (c[d])
#   - Otherwise, add 1 for the city c[d].
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

# Helper function: inCityOnDay
# Returns a condition that day d "includes" being in target city.
# On a flight day, the itinerary includes both the departure (c[d-1]) and arrival (c[d]).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event Constraints:
# Wedding in Stuttgart (city 1) between day 2 and day 3.
# That is, on day 2 (index 1) or day 3 (index 2) the itinerary should include Stuttgart.
wedding_event = [inCityOnDay(d, 1) for d in [1, 2]]
s.add(Or(wedding_event))

# Meeting friends at Split (city 2) between day 3 and day 4.
# That is, on day 3 (index 2) or day 4 (index 3) the itinerary should include Split.
friends_event = [inCityOnDay(d, 2) for d in [2, 3]]
s.add(Or(friends_event))

# Solve and print the itinerary
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        line = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            line += f" (Flight: {dep} -> {arr})"
        print(line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")