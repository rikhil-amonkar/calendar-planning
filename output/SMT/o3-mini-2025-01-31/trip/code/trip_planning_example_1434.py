from z3 import *

# City indices and names:
# 0: Rome       (3 days)
# 1: Mykonos    (2 days; event: meet friends at Mykonos between day 10 and day 11)
# 2: Lisbon     (2 days)
# 3: Frankfurt  (5 days; event: wedding in Frankfurt between day 1 and day 5)
# 4: Nice       (3 days)
# 5: Stuttgart  (4 days)
# 6: Venice     (4 days)
# 7: Dublin     (2 days)
# 8: Bucharest  (2 days)
# 9: Seville    (5 days; event: conference in Seville during day 13 and day 17)
city_names = ["Rome", "Mykonos", "Lisbon", "Frankfurt", "Nice", 
              "Stuttgart", "Venice", "Dublin", "Bucharest", "Seville"]

# Required day counts for each city.
req = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]
# Total required contributions = 3+2+2+5+3+4+4+2+2+5 = 32.
# We have 23 base days. When we take a flight on a day,
# that day contributes to two cities (the departure and the arrival).
# Thus, total contributions = 23 + (# flights). To achieve 32, we need 9 flights.
# The trip is segmented into 10 segments, each visited exactly one city.

# Allowed direct flights (bidirectional):
allowed_flights = [
    (0, 5), (5, 0),     # Rome <-> Stuttgart
    (6, 0), (0, 6),     # Venice <-> Rome
    (7, 8), (8, 7),     # Dublin <-> Bucharest
    (1, 0), (0, 1),     # Mykonos <-> Rome
    (9, 2), (2, 9),     # Seville <-> Lisbon
    (3, 6), (6, 3),     # Frankfurt <-> Venice
    (6, 5), (5, 6),     # Venice <-> Stuttgart
    (8, 2), (2, 8),     # Bucharest <-> Lisbon
    (4, 1), (1, 4),     # Nice <-> Mykonos
    (6, 2), (2, 6),     # Venice <-> Lisbon
    (7, 2), (2, 7),     # Dublin <-> Lisbon
    (6, 4), (4, 6),     # Venice <-> Nice
    (0, 9), (9, 0),     # Rome <-> Seville
    (3, 0), (0, 3),     # Frankfurt <-> Rome
    (4, 7), (7, 4),     # Nice <-> Dublin
    (0, 8), (8, 0),     # Rome <-> Bucharest
    (3, 7), (7, 3),     # Frankfurt <-> Dublin
    (0, 7), (7, 0),     # Rome <-> Dublin
    (6, 7), (7, 6),     # Venice <-> Dublin
    (0, 2), (2, 0),     # Rome <-> Lisbon
    (3, 2), (2, 3),     # Frankfurt <-> Lisbon
    (4, 0), (0, 4),     # Nice <-> Rome
    (3, 4), (4, 3),     # Frankfurt <-> Nice
    (3, 5), (5, 3),     # Frankfurt <-> Stuttgart
    (3, 8), (8, 3),     # Frankfurt <-> Bucharest
    (2, 5), (5, 2),     # Lisbon <-> Stuttgart
    (4, 2), (2, 4),     # Nice <-> Lisbon
    (9, 7), (7, 9)      # Seville <-> Dublin
]

# Total itinerary days.
DAYS = 23

# Create Z3 variables.
# c[d] represents the "base city" for day d (0-indexed, representing day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable for day d (d>=1) indicating whether a flight occurs on that day.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True when day d is the start of a new segment (always true for day 0 and for days with a flight).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city is among 0,...,9.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 10)

# Day 0 always starts a segment.
s.add(isSeg[0] == True)

# For d = 1,...,DAYS-1, define flight and segment indicator.
for d in range(1, DAYS):
    # Flight occurs on day d if the base city changes from previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d then the edge (c[d-1], c[d]) must be a direct flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 9 flights occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# The starting city of each segment (day 0 and each flight day) must be distinct,
# ensuring that every city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# (Optionally) enforce that every city appears at least once.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contributions" for each city.
# Day 0 contributes 1 to c[0].
# For each day d (1 <= d < DAYS):
#   if a flight occurs on day d, then add 1 for the departure (c[d-1]) and 1 for the arrival (c[d]);
#   otherwise add 1 for c[d] only.
counts = [Int(f"count_{i}") for i in range(10)]
for i in range(10):
    initial = If(c[0] == i, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               (If(c[d-1] == i, 1, 0) + If(c[d] == i, 1, 0)),
               If(c[d] == i, 1, 0)
            )
        )
    s.add(counts[i] == initial + Sum(daily))
    s.add(counts[i] == req[i])

# Helper: inCityOnDay(d, target) returns a condition that day d "includes" the target city.
# If a flight occurs on day d, then both the departure (d-1) and arrival (d) are counted.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Meet friends at Mykonos (city 1) between day 10 and day 11.
#    That is, on at least one day among day 10 and day 11 (indices 9 and 10), Mykonos is visited.
mykonos_event = [inCityOnDay(d, 1) for d in [9, 10]]
s.add(Or(mykonos_event))

# 2. Attend the wedding in Frankfurt (city 3) between day 1 and day 5.
#    That is, on at least one day among day 1 to day 5 (indices 0 through 4) Frankfurt is visited.
wedding_event = [inCityOnDay(d, 3) for d in range(0, 5)]
s.add(Or(wedding_event))

# 3. Attend the conference in Seville (city 9) during day 13 and day 17.
#    We assume this means on at least one of day 13 or day 17 the itinerary must include Seville.
#    (Using day 13 -> index 12 and day 17 -> index 16.)
conference_event = [inCityOnDay(d, 9) for d in [12, 16]]
s.add(Or(conference_event))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base = m[c[d]].as_long()
        line = f"Day {d+1:2d}: In {city_names[base]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base]
            line += f" (Flight: {dep} -> {arr})"
        print(line)
    print("\nCity day counts:")
    for i in range(10):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")