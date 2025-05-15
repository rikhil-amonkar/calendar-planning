from z3 import *

# Cities indexed as follows:
# 0: Naples
# 1: Valencia
# 2: Stuttgart
# 3: Split
# 4: Venice
# 5: Amsterdam
# 6: Nice
# 7: Barcelona
# 8: Porto
city_names = ["Naples", "Valencia", "Stuttgart", "Split", "Venice",
              "Amsterdam", "Nice", "Barcelona", "Porto"]

# Required day counts in each city.
# Naples: 3, Valencia: 5, Stuttgart: 2, Split: 5, Venice: 5,
# Amsterdam: 4, Nice: 2, Barcelona: 2, Porto: 4.
req = [3, 5, 2, 5, 5, 4, 2, 2, 4]

# Allowed direct flights.
# All pairs are bidirectional unless otherwise noted.
allowed_flights = [
    (4, 6), (6, 4),         # Venice and Nice
    (0, 5), (5, 0),         # Naples and Amsterdam
    (7, 6), (6, 7),         # Barcelona and Nice
    (5, 6), (6, 5),         # Amsterdam and Nice
    (2, 1), (1, 2),         # Stuttgart and Valencia
    (2, 8), (8, 2),         # Stuttgart and Porto
    (3, 2), (2, 3),         # Split and Stuttgart
    (3, 0), (0, 3),         # Split and Naples
    (1, 5), (5, 1),         # Valencia and Amsterdam
    (7, 8), (8, 7),         # Barcelona and Porto
    (1, 0), (0, 1),         # Valencia and Naples
    (4, 5), (5, 4),         # Venice and Amsterdam
    (7, 0), (0, 7),         # Barcelona and Naples
    (7, 1), (1, 7),         # Barcelona and Valencia
    (3, 5), (5, 3),         # Split and Amsterdam
    (7, 4), (4, 7),         # Barcelona and Venice
    (2, 5), (5, 2),         # Stuttgart and Amsterdam
    (0, 6), (6, 0),         # Naples and Nice
    (4, 2), (2, 4),         # Venice and Stuttgart
    (3, 7), (7, 3),         # Split and Barcelona
    (8, 6), (6, 8),         # Porto and Nice
    (7, 2), (2, 7),         # Barcelona and Stuttgart
    (4, 0), (0, 4),         # Venice and Naples
    (8, 5), (5, 8),         # Porto and Amsterdam
    (8, 1), (1, 8),         # Porto and Valencia
    (2, 0), (0, 2),         # Stuttgart and Naples
    (7, 5), (5, 7)          # Barcelona and Amsterdam
]

# Total number of days in the itinerary.
DAYS = 24

# Since the travel plan "base days" are 24, and if on a flight day you get
# an extra count for the departure city, the total day-count equals 24 + (#flights).
# Our required total count is sum(req) = 3+5+2+5+5+4+2+2+4 = 32.
# Thus the number of flights must be: 32 - 24 = 8.
#
# And since each flight corresponds to switching the "base city" (and so a new segment),
# we will have 9 segments visiting 9 distinct cities.

# Create Z3 variables.
# c[d] is the "base city" for day d (0-indexed, corresponding to day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True when on day d (d>=1) a flight occurs (i.e. c[d] != c[d-1]).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 always, and any day with flight).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be one of our 9 cities.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 9))

# Day 0 is automatically the start of a segment.
s.add(isSeg[0] == True)

# For days 1 .. 23, define flight indicator and if flight occurs, the flight must be allowed.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then (c[d-1], c[d]) must be an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Exactly 8 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 8)

# The cities at the start of each segment (day 0 and each day when a flight occurs)
# must be distinct (ensuring that we visit 9 different cities).
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# (Optional) Enforce that each city appears at least once in the plan.
for city in range(9):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contribution" for each city.
# On day 0, the traveler is in city c[0].
# For day d>=1:
#   - if no flight: only c[d] gets count 1,
#   - if flight occurs: both c[d-1] (departure) and c[d] (arrival) get count 1.
counts = [Int(f"count_{city}") for city in range(9)]
for city in range(9):
    base = If(c[0] == city, 1, 0)
    contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        contribs.append(contrib)
    s.add(counts[city] == base + Sum(contribs))
    s.add(counts[city] == req[city])

# Define helper function for "inCityOnDay".
# On day d:
#  - If d == 0: the traveler is in city c[0].
#  - For d >= 1:
#       If flight occurs on that day, the traveler is in either c[d-1] or c[d].
#       Otherwise, the traveler is in c[d].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints:

# 1. In Naples (city 0), meet a friend between day 18 and day 20 (i.e. days 18..20, indices 17..19).
friend_naples = [inCityOnDay(d, 0) for d in range(17, 20)]
s.add(Or(friend_naples))

# 2. In Venice (city 4), attend a conference on day 6 and day 10.
s.add(inCityOnDay(5, 4))  # day6: index 5
s.add(inCityOnDay(9, 4))  # day10: index 9

# 3. In Barcelona (city 7), attend a workshop between day 5 and day 6 (indices 4 and 5).
workshop_barcelona = [inCityOnDay(d, 7) for d in range(4, 6)]
s.add(Or(workshop_barcelona))

# 4. In Nice (city 6), meet your friends between day 23 and day 24 (indices 22 and 23).
friends_nice = [inCityOnDay(d, 6) for d in range(22, 24)]
s.add(Or(friends_nice))

# At this point, we have encoded:
# - The day counts for each city, forcing exactly 8 flights (9 segments),
# - All flights must be allowed,
# - And extra event constraints (friend meeting, conference, workshop, tour meeting).

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        day_info = f"Day {d+1:2d}: In {city_names[m[c[d]].as_long()]}"
        if d >= 1 and m.evaluate(flight[d]):
            day_info += f" (Flight: {city_names[m[c[d-1]].as_long()]} -> {city_names[m[c[d]].as_long()]})"
        print(day_info)
    print("\nCity day counts:")
    for city in range(9):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")