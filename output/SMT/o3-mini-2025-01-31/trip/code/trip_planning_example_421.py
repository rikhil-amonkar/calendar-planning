from z3 import *

# Cities (indices):
# 0: Nice (5 days, relatives event between day 1 and day 5)
# 1: Krakow (6 days)
# 2: Dublin (7 days)
# 3: Lyon (4 days)
# 4: Frankfurt (2 days, friends event between day 19 and day 20)
city_names = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]

# Required day counts for each city:
req = [5, 6, 7, 4, 2]

# Allowed direct flights:
# - Nice and Dublin (bidirectional): (0,2) and (2,0)
# - Dublin and Frankfurt (bidirectional): (2,4) and (4,2)
# - Dublin and Krakow (bidirectional): (2,1) and (1,2)
# - Krakow and Frankfurt (bidirectional): (1,4) and (4,1)
# - Lyon and Frankfurt (bidirectional): (3,4) and (4,3)
# - Nice and Frankfurt (bidirectional): (0,4) and (4,0)
# - Lyon and Dublin (bidirectional): (3,2) and (2,3)
# - Nice and Lyon (bidirectional): (0,3) and (3,0)
allowed_flights = [
    (0,2), (2,0),
    (2,4), (4,2),
    (2,1), (1,2),
    (1,4), (4,1),
    (3,4), (4,3),
    (0,4), (4,0),
    (3,2), (2,3),
    (0,3), (3,0)
]

# Total itinerary days.
DAYS = 20

# The sum of required days is 5 + 6 + 7 + 4 + 2 = 24.
# The day contribution equals (# base days) + (# flights).
# Therefore, let f be the number of flights. 20 + f = 24, hence f = 4.
# With 4 flights there are 5 segments, which must correspond to the 5 different cities.
# In a flight day, one is counted in both the departure city and the arrival city.
#
# Create Z3 variables.
# c[d] is the "base city" on day d (0-indexed for day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that is true when on day d (d>=1) a flight occurs (i.e. c[d] != c[d-1]).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates that day d is the start of a new segment.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city is one of the 5 cities.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 5))

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1 through DAYS-1, set flight indicator and permitted flights.
for d in range(1, DAYS):
    # Flight occurs if the base city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs then the pair (c[d-1], c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Exactly 4 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# The cities at the start of each segment (day0 and each flight day) must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, enforce that each city appears at least once.
for city in range(5):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contribution" for each city.
# On day 0, the traveler is in city c[0] (contributing 1 to that city).
# For each day d >= 1:
#   - if there's no flight: add 1 for city c[d];
#   - if there's a flight: add 1 for c[d-1] (departure) and 1 for c[d] (arrival).
counts = [Int(f"count_{city}") for city in range(5)]
for city in range(5):
    day0_contrib = If(c[0] == city, 1, 0)
    daily_contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        daily_contribs.append(contrib)
    s.add(counts[city] == day0_contrib + Sum(daily_contribs))
    s.add(counts[city] == req[city])

# Helper function: on a given day, the itinerary "includes" a target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints:
# 1. Visit relatives in Nice (city 0) between day 1 and day 5 (days 1..5; indices 0..4).
relatives_nice = [inCityOnDay(d, 0) for d in range(0, 5)]
s.add(Or(relatives_nice))

# 2. Meet friends at Frankfurt (city 4) between day 19 and day 20 (days 19..20; indices 18 and 19).
friends_frankfurt = [inCityOnDay(d, 4) for d in range(18, 20)]
s.add(Or(friends_frankfurt))

# Check the model and output a valid itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        line = f"Day {d+1:2d}: {city_names[m[c[d]].as_long()]}"
        if d >= 1 and m.evaluate(flight[d]):
            line += f" (Flight: {city_names[m[c[d-1]].as_long()]} -> {city_names[m[c[d]].as_long()]})"
        print(line)
    print("\nCity day counts:")
    for city in range(5):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")