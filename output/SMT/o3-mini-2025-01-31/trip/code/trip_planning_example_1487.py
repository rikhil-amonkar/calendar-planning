from z3 import *

# City indices and names:
# 0: Copenhagen   (5 days; event: meet friend between day 11 and day 15)
# 1: Geneva       (3 days)
# 2: Mykonos      (2 days; event: attend conference on day 27 and day 28)
# 3: Naples       (4 days; event: visit relatives between day 5 and day 8)
# 4: Prague       (2 days)
# 5: Dubrovnik    (3 days)
# 6: Athens       (4 days; event: attend workshop between day 8 and day 11)
# 7: Santorini    (5 days)
# 8: Brussels     (4 days)
# 9: Munich       (5 days)
city_names = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]

# Required day counts for each city:
req = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]

# Total required contributions = 5+3+2+4+2+3+4+5+4+5 = 37.
# We have 28 base days.
# Days contributed = 28 + (# flights), so we must have 28 + f = 37, i.e. f = 9 flights.
# That implies the trip is segmented into 10 segments, each assigned to a unique city.

# Allowed direct flights, given as bidirectional pairs:
allowed_flights = [
    # Copenhagen and Dubrovnik
    (0, 5), (5, 0),
    # Brussels and Copenhagen
    (8, 0), (0, 8),
    # Prague and Geneva
    (4, 1), (1, 4),
    # Athens and Geneva
    (6, 1), (1, 6),
    # Naples and Dubrovnik
    (3, 5), (5, 3),
    # Athens and Dubrovnik
    (6, 5), (5, 6),
    # Geneva and Mykonos
    (1, 2), (2, 1),
    # Naples and Mykonos
    (3, 2), (2, 3),
    # Naples and Copenhagen
    (3, 0), (0, 3),
    # Munich and Mykonos
    (9, 2), (2, 9),
    # Naples and Athens
    (3, 6), (6, 3),
    # Prague and Athens
    (4, 6), (6, 4),
    # Santorini and Geneva
    (7, 1), (1, 7),
    # Athens and Santorini
    (6, 7), (7, 6),
    # Naples and Munich
    (3, 9), (9, 3),
    # Prague and Copenhagen
    (4, 0), (0, 4),
    # Brussels and Naples
    (8, 3), (3, 8),
    # Athens and Mykonos
    (6, 2), (2, 6),
    # Athens and Copenhagen
    (6, 0), (0, 6),
    # Naples and Geneva
    (3, 1), (1, 3),
    # Dubrovnik and Munich
    (5, 9), (9, 5),
    # Brussels and Munich
    (8, 9), (9, 8),
    # Prague and Brussels
    (4, 8), (8, 4),
    # Brussels and Athens
    (8, 6), (6, 8),
    # Athens and Munich
    (6, 9), (9, 6),
    # Geneva and Munich
    (1, 9), (9, 1),
    # Copenhagen and Munich
    (0, 9), (9, 0),
    # Brussels and Geneva
    (8, 1), (1, 8),
    # Copenhagen and Geneva
    (0, 1), (1, 0),
    # Prague and Munich
    (4, 9), (9, 4),
    # Copenhagen and Santorini
    (0, 7), (7, 0),
    # Naples and Santorini
    (3, 7), (7, 3),
    # Geneva and Dubrovnik
    (1, 5), (5, 1)
]

# Total itinerary days.
DAYS = 28

# Create Z3 variables:
# c[d] represents the "base city" on day d (for day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean (for d>=1) indicating a flight occurs on day d.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a segment (either day 0 or a flight day).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be one of 0,...,9.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 10))

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1..DAYS-1, define flight indicators and allowed flight constraints.
for d in range(1, DAYS):
    # A flight occurs on day d if c[d] != c[d-1].
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 9 flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# The starting city of each segment (day 0 and any day a flight occurs) must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# (Optionally) Enforce that each city appears at least once.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contributions" for each city.
# On day 0, contribution is 1 for city c[0].
# For each day d (1 to DAYS-1):
#   If flight occurs on day d, add 1 for c[d-1] and 1 for c[d];
#   else add 1 for c[d].
counts = [Int(f"count_{city}") for city in range(10)]
for city in range(10):
    base = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(If(flight[d],
                        If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                        If(c[d] == city, 1, 0)))
    s.add(counts[city] == base + Sum(daily))
    s.add(counts[city] == req[city])

# Helper: inCityOnDay(d, target) enforces that on day d the itinerary "includes" target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:
# 1. Meet friend in Copenhagen (city 0) between day 11 and day 15 (indices 10..14).
friend_copenhagen = [inCityOnDay(d, 0) for d in range(10, 15)]
s.add(Or(friend_copenhagen))

# 2. Attend conference in Mykonos (city 2) on day 27 and day 28 (indices 26 and 27).
conference_mykonos = [inCityOnDay(d, 2) for d in [26, 27]]
s.add(Or(conference_mykonos))

# 3. Visit relatives in Naples (city 3) between day 5 and day 8 (indices 4..7).
relatives_naples = [inCityOnDay(d, 3) for d in range(4, 8)]
s.add(Or(relatives_naples))

# 4. Attend workshop in Athens (city 6) between day 8 and day 11 (indices 7..10).
workshop_athens = [inCityOnDay(d, 6) for d in range(7, 11)]
s.add(Or(workshop_athens))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: In {city_names[base]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for city in range(10):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")