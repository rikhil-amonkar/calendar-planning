from z3 import *

# City indices and requirements:
# 0: Riga    – 7 days; event: attend a wedding in Riga between day 11 and day 17.
# 1: Budapest– 7 days.
# 2: Paris   – 4 days.
# 3: Warsaw  – 2 days; event: attend an annual show in Warsaw between day 1 and day 2.
city_names = ["Riga", "Budapest", "Paris", "Warsaw"]
req = [7, 7, 4, 2]  # Total day contributions required = 20

# The trip lasts 17 days (indexed 0 to 16). On non-flight days the city gets 1 day credit.
# If a flight occurs on a day, both the departure and arrival get credit.
# Therefore, total credits = base_days + (# flights).
# We have 20 required credits and 17 base days, so we need exactly 3 flights.
# With 3 flights the itinerary is partitioned into 4 segments, one for each city.
DAYS = 17

# Allowed direct flights.
# Unless noted as one-way ("from X to Y"), assume bidirectional.
# Cities are indexed as: Riga=0, Budapest=1, Paris=2, Warsaw=3.
allowed_flights = [
    # Warsaw and Budapest
    (3,1), (1,3),
    # Warsaw and Riga
    (3,0), (0,3),
    # Budapest and Paris
    (1,2), (2,1),
    # Warsaw and Paris
    (3,2), (2,3),
    # Paris and Riga
    (2,0), (0,2)
]

# Create variables.
# c[d] is the "base" city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (for d>=1; day 0 has no flight).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates that day d is the start of a segment (day 0 or a flight day).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each day's base city is in {0,1,2,3}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is the start of a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1, define whether a flight occurs.
for d in range(1, DAYS):
    # A flight occurs if the base city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the transition must be among allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 3 flights in total.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 3)

# 5. The starting city of each segment (day 0 and days with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce each city is visited (since we need 4 segments and have 4 cities).
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute the day contributions:
# Day 0 gives a credit to c[0].
# For d>=1, if flight happens, then both departure and arrival get credit.
# Otherwise, only the current day's city gets a credit.
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    contrib = []
    for d in range(1, DAYS):
        contrib.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(contrib))
    # Enforce each city's required number of days.
    s.add(counts[city] == req[city])

# Helper: on day d, check if itinerary "includes" target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints.
# (a) Wedding in Riga (city 0) between day 11 and day 17: indices 10 to 16.
wedding_event = [inCityOnDay(d, 0) for d in range(10, DAYS)]
s.add(Or(wedding_event))

# (b) Annual show in Warsaw (city 3) between day 1 and day 2: indices 0 and 1.
annual_show = [inCityOnDay(d, 3) for d in range(0, 2)]
s.add(Or(annual_show))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        line = f"Day {d+1:2d}: {city_names[city_idx]}"
        # If a flight took place on this day, add flight information.
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