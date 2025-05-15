from z3 import *

# City indices and requirements:
# 0: Valencia  – 5 days.
# 1: Riga      – 5 days.
# 2: Prague    – 3 days; event: visit relatives in Prague between day 7 and day 9.
# 3: Mykonos   – 3 days; event: attend a wedding in Mykonos between day 1 and day 3.
# 4: Zurich    – 5 days.
# 5: Bucharest – 5 days.
# 6: Nice      – 2 days.
city_names = ["Valencia", "Riga", "Prague", "Mykonos", "Zurich", "Bucharest", "Nice"]
req = [5, 5, 3, 3, 5, 5, 2]  # Total required day credits = 5+5+3+3+5+5+2 = 28

# Total base days = 22.
# Each non-flight day gives 1 credit.
# Each flight day (i.e. when you fly, you get credit for both departure and arrival) adds 1 extra credit.
# Thus, total credits = 22 + (# flights).
# To have 28 total credits, we need exactly 6 flights.
# With 6 flights, the itinerary splits into 7 segments, one per city.
DAYS = 22

# Allowed direct flights (bidirectional):
# Mykonos and Nice         -> (3,6) and (6,3)
# Mykonos and Zurich       -> (3,4) and (4,3)
# Prague and Bucharest     -> (2,5) and (5,2)
# Valencia and Bucharest   -> (0,5) and (5,0)
# Zurich and Prague        -> (4,2) and (2,4)
# Riga and Nice            -> (1,6) and (6,1)
# Zurich and Riga          -> (4,1) and (1,4)
# Zurich and Bucharest     -> (4,5) and (5,4)
# Zurich and Valencia      -> (4,0) and (0,4)
# Bucharest and Riga       -> (5,1) and (1,5)
# Prague and Riga          -> (2,1) and (1,2)
# Prague and Valencia      -> (2,0) and (0,2)
# Zurich and Nice          -> (4,6) and (6,4)
allowed_flights = [
    (3,6), (6,3),
    (3,4), (4,3),
    (2,5), (5,2),
    (0,5), (5,0),
    (4,2), (2,4),
    (1,6), (6,1),
    (4,1), (1,4),
    (4,5), (5,4),
    (4,0), (0,4),
    (5,1), (1,5),
    (2,1), (1,2),
    (2,0), (0,2),
    (4,6), (6,4)
]

# Create Z3 variables:
# c[d]: the base city (the city you are "in") on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: True if a flight occurs on day d (d>=1, day 0 has no flight).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: True if day d is the start of a new segment (either day 0 or when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain for city variables.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 always starts a segment.
s.add(isSeg[0] == True)

# 3. For days d>=1, define flight occurrence.
for d in range(1, DAYS):
    # A flight occurs if the base city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # When a flight occurs, assert that (c[d-1], c[d]) is an allowed direct flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 6 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# 5. Distinct segments constraint:
# The starting base cities of the segments (day 0 and any day with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that each city is visited (each city must be the starting city of some segment).
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions:
# Day 0 gives 1 credit to c[0].
# For each day d>=1:
#   - If a flight occurs, both the previous day's city (c[d-1]) and current day's city (c[d]) get a credit.
#   - Otherwise, only the current day's city gets 1 credit.
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

# Helper: on day d, the itinerary "includes" a target city.
# If a flight occurs, then both the departure (previous day) and arrival (day d) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Wedding in Mykonos (city 3) between day 1 and day 3:
#     This means for some day in indices 0 to 2 the itinerary includes Mykonos.
wedding_event = [inCityOnDay(d, 3) for d in range(0, 3)]
s.add(Or(wedding_event))

# (b) Visit relatives in Prague (city 2) between day 7 and day 9:
#     That is, for some day in indices 6 to 8 the itinerary includes Prague.
prague_event = [inCityOnDay(d, 2) for d in range(6, 9)]
s.add(Or(prague_event))

# Solve the model and print the itinerary.
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