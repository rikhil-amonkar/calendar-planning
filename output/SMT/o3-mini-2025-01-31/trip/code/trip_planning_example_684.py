from z3 import *

# City indices and names:
# 0: Amsterdam   (4 days; event: visit relatives in Amsterdam between day 5 and day 8)
# 1: Edinburgh   (5 days)
# 2: Brussels    (5 days)
# 3: Vienna      (5 days)
# 4: Berlin      (4 days; event: meet a friend in Berlin between day 16 and day 19)
# 5: Reykjavik   (5 days; event: attend workshop in Reykjavik between day 12 and day 16)
city_names = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]

# Required day counts per city.
req = [4, 5, 5, 5, 4, 5]
# Total required contributions = 4+5+5+5+4+5 = 28.
# We have 23 base days.
# Total contributions = base days (23) + (# flights).
# To have 23 + f = 28, we require f = 5 flights.
# That means the trip is divided into 6 segments (each visited exactly one city).

# Allowed direct flights (bidirectional):
allowed_flights = [
    (1, 4), (4, 1),   # Edinburgh <-> Berlin
    (0, 4), (4, 0),   # Amsterdam <-> Berlin
    (1, 0), (0, 1),   # Edinburgh <-> Amsterdam
    (3, 4), (4, 3),   # Vienna <-> Berlin
    (4, 2), (2, 4),   # Berlin <-> Brussels
    (3, 5), (5, 3),   # Vienna <-> Reykjavik
    (1, 2), (2, 1),   # Edinburgh <-> Brussels
    (3, 2), (2, 3),   # Vienna <-> Brussels
    (0, 5), (5, 0),   # Amsterdam <-> Reykjavik
    (5, 2), (2, 5),   # Reykjavik <-> Brussels
    (0, 3), (3, 0),   # Amsterdam <-> Vienna
    (5, 4), (4, 5)    # Reykjavik <-> Berlin
]

# Total itinerary days.
DAYS = 23

# Create Z3 variables.
# c[d] represents the "base city" for day d (0-indexed for day d+1). 
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that indicates if a flight occurs on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment: day 0 always, and any day when flight occurs.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be in {0,...,5}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 6)

# Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight occurrence.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then the traveled edge must be among allowed flights.
    s.add(Implies(flight[d], 
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Exactly 5 flights should occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 5)

# The starting city of each segment (day 0 and every flight day) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited.
for city in range(6):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# On day 0, add 1 for the base city c[0].
# For each day d from 1 to DAYS-1:
#   If a flight occurs, add 1 to the departure city (c[d-1]) and 1 to the arrival city (c[d]).
#   Otherwise, add 1 for the base city on that day.
counts = [Int(f"count_{city}") for city in range(6)]
for city in range(6):
    initial = If(c[0] == city, 1, 0)
    daily_contrib = []
    for d in range(1, DAYS):
        daily_contrib.append(
            If(flight[d],
               (If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0)),
               If(c[d] == city, 1, 0)
            ))
    s.add(counts[city] == initial + Sum(daily_contrib))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay(d, target) returns a condition that day d includes the target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:
# 1. Visit relatives in Amsterdam (city 0) between day 5 and day 8.
# Days 5 to 8 correspond to indices 4,5,6,7.
relatives_amsterdam = [inCityOnDay(d, 0) for d in range(4, 8)]
s.add(Or(relatives_amsterdam))

# 2. Attend workshop in Reykjavik (city 5) between day 12 and day 16.
# Days 12 to 16 correspond to indices 11,12,13,14,15.
workshop_reykjavik = [inCityOnDay(d, 5) for d in range(11, 16)]
s.add(Or(workshop_reykjavik))

# 3. Meet a friend in Berlin (city 4) between day 16 and day 19.
# Days 16 to 19 correspond to indices 15,16,17,18.
friend_berlin = [inCityOnDay(d, 4) for d in range(15, 19)]
s.add(Or(friend_berlin))

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
    for city in range(6):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")