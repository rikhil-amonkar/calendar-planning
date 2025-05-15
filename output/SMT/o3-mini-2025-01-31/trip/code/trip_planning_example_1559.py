from z3 import *

# Cities (index: city_name, required days, event if any):
# 0: Valencia   -> 2 days; event: meet friends at Valencia between day 3 and day 4.
# 1: Oslo       -> 3 days; event: meet friend in Oslo between day 13 and day 15.
# 2: Lyon       -> 4 days.
# 3: Prague     -> 3 days.
# 4: Paris      -> 4 days.
# 5: Nice       -> 4 days.
# 6: Seville    -> 5 days; event: annual show in Seville from day 5 to day 9.
# 7: Tallinn    -> 2 days.
# 8: Mykonos    -> 5 days; event: wedding in Mykonos between day 21 and day 25.
# 9: Lisbon     -> 2 days.
city_names = ["Valencia", "Oslo", "Lyon", "Prague", "Paris", "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"]
req = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]

# Total day contributions required = sum(req) = 34.
# Base days = 25, so extra contributions must come from flights.
# Each flight day contributes an extra day (departure and arrival count).
# So #flights = 34 - 25 = 9.
# This splits the trip into 10 segments (one segment per visited city).

DAYS = 25

# Allowed direct flights (bidirectional). We list each pair with both directions.
# - Lisbon and Paris
# - Lyon and Nice
# - Tallinn and Oslo
# - Prague and Lyon
# - Paris and Oslo
# - Lisbon and Seville
# - Prague and Lisbon
# - Oslo and Nice
# - Valencia and Paris
# - Valencia and Lisbon
# - Paris and Nice
# - Nice and Mykonos
# - Paris and Lyon
# - Valencia and Lyon
# - Prague and Oslo
# - Prague and Paris
# - Seville and Paris
# - Oslo and Lyon
# - Prague and Valencia
# - Lisbon and Nice
# - Lisbon and Oslo
# - Valencia and Seville
# - Lisbon and Lyon
# - Paris and Tallinn
# - Prague and Tallinn
allowed_flights = [
    (9, 4), (4, 9),      # Lisbon <-> Paris
    (2, 5), (5, 2),      # Lyon <-> Nice
    (7, 1), (1, 7),      # Tallinn <-> Oslo
    (3, 2), (2, 3),      # Prague <-> Lyon
    (4, 1), (1, 4),      # Paris <-> Oslo
    (9, 6), (6, 9),      # Lisbon <-> Seville
    (3, 9), (9, 3),      # Prague <-> Lisbon
    (1, 5), (5, 1),      # Oslo <-> Nice
    (0, 4), (4, 0),      # Valencia <-> Paris
    (0, 9), (9, 0),      # Valencia <-> Lisbon
    (4, 5), (5, 4),      # Paris <-> Nice
    (5, 8), (8, 5),      # Nice <-> Mykonos
    (4, 2), (2, 4),      # Paris <-> Lyon
    (0, 2), (2, 0),      # Valencia <-> Lyon
    (3, 1), (1, 3),      # Prague <-> Oslo
    (3, 4), (4, 3),      # Prague <-> Paris
    (6, 4), (4, 6),      # Seville <-> Paris
    (1, 2), (2, 1),      # Oslo <-> Lyon
    (3, 0), (0, 3),      # Prague <-> Valencia
    (9, 5), (5, 9),      # Lisbon <-> Nice
    (9, 1), (1, 9),      # Lisbon <-> Oslo
    (0, 6), (6, 0),      # Valencia <-> Seville
    (9, 2), (2, 9),      # Lisbon <-> Lyon
    (4, 7), (7, 4),      # Paris <-> Tallinn
    (3, 7), (7, 3)       # Prague <-> Tallinn
]

# Create Z3 variables:
# c[d] is the base city on day d (0-indexed: day d corresponds to real day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean indicating whether a flight occurs on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 or day with flight).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: For each day, the base city must be one of 0..9.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 10)

# 2. Day 0 is always the start of a new segment.
s.add(isSeg[0] == True)

# 3. For days 1 to 24, define flights and segment-start conditions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # And day d is a segment start if a flight took place.
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, (c[d-1], c[d]) must be a permitted direct flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 9 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# 5. Enforce that the start of each segment (day 0 and every flight day) are distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, require each city is visited at least once.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 gives a contribution of 1 for c[0].
# For each day d (d>=1):
#   if flight occurs then add 1 for departure (c[d-1]) and 1 for arrival (c[d]),
#   otherwise add 1 for city c[d] only.
counts = [Int(f"count_{city}") for city in range(10)]
for city in range(10):
    init = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(daily))
    s.add(counts[city] == req[city])

# Helper function: returns a condition that day d "includes" the target city.
# On a flight day, both the departure and arrival are considered.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# Event 1: Meet friends at Valencia (city 0) between day 3 and day 4.
# Days 3 and 4 correspond to indices 2 and 3.
valencia_event = [inCityOnDay(d, 0) for d in [2, 3]]
s.add(Or(valencia_event))

# Event 2: Meet a friend in Oslo (city 1) between day 13 and day 15.
# Days 13, 14, 15 correspond to indices 12, 13, 14.
oslo_event = [inCityOnDay(d, 1) for d in [12, 13, 14]]
s.add(Or(oslo_event))

# Event 3: Annual show in Seville (city 6) from day 5 to day 9.
# Days 5 to 9 are indices 4, 5, 6, 7, 8.
seville_event = [inCityOnDay(d, 6) for d in range(4, 9)]
s.add(Or(seville_event))

# Event 4: Wedding in Mykonos (city 8) between day 21 and day 25.
# Days 21 to 25 are indices 20, 21, 22, 23, 24.
mykonos_event = [inCityOnDay(d, 8) for d in range(20, 25)]
s.add(Or(mykonos_event))

# Solve and print the itinerary if found.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_index = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_index]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_index]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(10):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")