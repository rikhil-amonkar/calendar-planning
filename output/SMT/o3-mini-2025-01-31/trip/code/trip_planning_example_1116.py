from z3 import *

# City indices and names:
# 0: Oslo        (2 days; event: annual show in Oslo from day 16 to day 17)
# 1: Reykjavik   (5 days; event: meet a friend in Reykjavik between day 9 and day 13)
# 2: Stockholm   (4 days)
# 3: Munich      (4 days; event: visit relatives in Munich between day 13 and day 16)
# 4: Frankfurt   (4 days; event: workshop in Frankfurt between day 17 and day 20)
# 5: Barcelona   (3 days)
# 6: Bucharest   (2 days)
# 7: Split       (3 days)
city_names = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]

# Required day counts for each city.
req = [2, 5, 4, 4, 4, 3, 2, 3]

# Sum of required days = 2+5+4+4+4+3+2+3 = 27.
# With 20 base days and extra day contribution on flight days,
# total contributions = 20 + (# flights). Hence we must have f flights s.t.
# 20 + f = 27, so f = 7.
# This gives 8 segments (start of each segment) that correspond to the 8 distinct cities.

# Allowed direct flights (each tuple is (from, to)).
# For bidirectional connections both orders are allowed.
allowed_flights = [
    # Reykjavik and Munich
    (1, 3), (3, 1),
    # Munich and Frankfurt
    (3, 4), (4, 3),
    # Split and Oslo
    (7, 0), (0, 7),
    # Reykjavik and Oslo
    (1, 0), (0, 1),
    # Bucharest and Munich
    (6, 3), (3, 6),
    # Oslo and Frankfurt
    (0, 4), (4, 0),
    # Bucharest and Barcelona
    (6, 5), (5, 6),
    # Barcelona and Frankfurt
    (5, 4), (4, 5),
    # Reykjavik and Frankfurt
    (1, 4), (4, 1),
    # Barcelona and Stockholm
    (5, 2), (2, 5),
    # Barcelona and Reykjavik
    (5, 1), (1, 5),
    # Stockholm and Reykjavik
    (2, 1), (1, 2),
    # Barcelona and Split
    (5, 7), (7, 5),
    # Bucharest and Oslo
    (6, 0), (0, 6),
    # Bucharest and Frankfurt
    (6, 4), (4, 6),
    # Split and Stockholm
    (7, 2), (2, 7),
    # Barcelona and Oslo
    (5, 0), (0, 5),
    # Stockholm and Munich
    (2, 3), (3, 2),
    # Stockholm and Oslo
    (2, 0), (0, 2),
    # Split and Frankfurt
    (7, 4), (4, 7),
    # Barcelona and Munich
    (5, 3), (3, 5),
    # Stockholm and Frankfurt
    (2, 4), (4, 2),
    # Munich and Oslo
    (3, 0), (0, 3),
    # Split and Munich
    (7, 3), (3, 7)
]

# Total itinerary days.
DAYS = 20

# Create Z3 variables:
# c[d] is the "base city" on day d (0-indexed, representing day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable for d>=1 indicating that a flight occurs on day d
# (i.e. when c[d] differs from c[d-1]).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (either day 0 or when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be one of the 8 cities.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 8))

# Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight indicators and enforce allowed flight constraints.
for d in range(1, DAYS):
    # A flight occurs if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then (c[d-1], c[d]) must be in allowed_flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Enforce exactly 7 flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 7)

# The cities at the start of each segment (day 0 and every flight day) must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, enforce that each city appears at least once.
for city in range(8):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contributions" for each city:
# On day 0, the traveler contributes 1 (in city c[0]).
# For each day d (1 to DAYS-1):
#   if no flight: add 1 to city c[d];
#   if flight: add 1 to c[d-1] (departure) and 1 to c[d] (arrival).
counts = [Int(f"count_{city}") for city in range(8)]
for city in range(8):
    base = If(c[0] == city, 1, 0)
    daily_contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        daily_contribs.append(contrib)
    s.add(counts[city] == base + Sum(daily_contribs))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay(d, target) returns a condition that on day d the itinerary "includes" target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints:

# 1. Annual show in Oslo (city 0) between day 16 and day 17.
#    That is, at least one day among days 16 and 17 (indices 15 and 16) must include Oslo.
oslo_show = [inCityOnDay(d, 0) for d in [15, 16]]
s.add(Or(oslo_show))

# 2. Meet a friend in Reykjavik (city 1) between day 9 and day 13.
#    That is, at least one day among days 9 to 13 (indices 8 to 12) must include Reykjavik.
friend_reykjavik = [inCityOnDay(d, 1) for d in range(8, 13)]
s.add(Or(friend_reykjavik))

# 3. Visit relatives in Munich (city 3) between day 13 and day 16.
#    That is, at least one day among days 13 to 16 (indices 12 to 15) must include Munich.
relatives_munich = [inCityOnDay(d, 3) for d in range(12, 16)]
s.add(Or(relatives_munich))

# 4. Attend a workshop in Frankfurt (city 4) between day 17 and day 20.
#    That is, at least one day among days 17 to 20 (indices 16 to 19) must include Frankfurt.
workshop_frankfurt = [inCityOnDay(d, 4) for d in range(16, 20)]
s.add(Or(workshop_frankfurt))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        day_str = f"Day {d+1:2d}: In {city_names[m[c[d]].as_long()]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[m[c[d]].as_long()]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for city in range(8):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")