from z3 import *

# Cities (indices and names):
# 0: Hamburg
# 1: Munich
# 2: Manchester
# 3: Lyon
# 4: Split
city_names = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]

# Required day counts in each city:
# Hamburg: 7, Munich: 6, Manchester: 2, Lyon: 2, Split: 7.
req = [7, 6, 2, 2, 7]

# Allowed flights.
# Explanation:
# • "Split and Munich": allow (4,1) and (1,4)
# • "Munich and Manchester": allow (1,2) and (2,1)
# • "Hamburg and Manchester": allow (0,2) and (2,0)
# • "Hamburg and Munich": allow (0,1) and (1,0)
# • "Split and Lyon": allow (4,3) and (3,4)
# • "Lyon and Munich": allow (3,1) and (1,3)
# • "Hamburg and Split": allow (0,4) and (4,0)
# • "from Manchester to Split": allow only (2,4) [unidirectional].
allowed_flights = [
    (4, 1), (1, 4),       # Split <-> Munich
    (1, 2), (2, 1),       # Munich <-> Manchester
    (0, 2), (2, 0),       # Hamburg <-> Manchester
    (0, 1), (1, 0),       # Hamburg <-> Munich
    (4, 3), (3, 4),       # Split <-> Lyon
    (3, 1), (1, 3),       # Lyon <-> Munich
    (0, 4), (4, 0),       # Hamburg <-> Split
    (2, 4)                # Manchester -> Split (only this direction)
]

# Total number of days in the itinerary.
DAYS = 20

# The required total day count is:
# Hamburg (7) + Munich (6) + Manchester (2) + Lyon (2) + Split (7) = 24.
# But we have 20 base days and extra count(s) for flights.
# If we fly on f days then total count = 20 + f.
# Thus we require: 20 + f = 24  ==> f = 4.
# With 4 flights we get 5 segments (for 5 distinct cities).

# Create Z3 variables:
# c[d] is the "base city" on day d (0-indexed, i.e. day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if on day d (d>=1) a flight occurs (i.e. c[d] != c[d-1]).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day0 and whenever a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city is between 0 and 4.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 5))

# Day 0 is a segment start.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight indicator and enforce allowed flights.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Exactly 4 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# The cities at the start of each segment (day 0 and each flight day) must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, enforce that each city appears at least once in the itinerary.
for city in range(5):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contribution" for each city.
# On day 0, the traveler is in c[0] (1 count);
# For each day d >= 1:
#   If no flight: 1 count for c[d];
#   If flight: 1 count for c[d-1] (departure) and 1 count for c[d] (arrival).
counts = [Int(f"count_{city}") for city in range(5)]
for city in range(5):
    day0 = If(c[0] == city, 1, 0)
    contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        contribs.append(contrib)
    s.add(counts[city] == day0 + Sum(contribs))
    s.add(counts[city] == req[city])

# Helper function: on day d, the itinerary "includes" a given city.
# On day 0: must be c[0] == target;
# For d >= 1: if flight[d] then traveler is in c[d-1] or c[d], otherwise just in c[d].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints:
# 1. Relatives in Manchester (city 2) between day 19 and day 20
#    (i.e. at least one day among day indices 18 and 19).
relatives_manchester = [inCityOnDay(d, 2) for d in range(18, 20)]
s.add(Or(relatives_manchester))

# 2. Annual show in Lyon (city 3) from day 13 to day 14
#    (i.e. at least one day among day indices 12 and 13).
annual_show_lyon = [inCityOnDay(d, 3) for d in range(12, 14)]
s.add(Or(annual_show_lyon))

# Check for solution and print itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        day_str = f"Day {d+1:2d}: In {city_names[m[c[d]].as_long()]}"
        if d >= 1 and m.evaluate(flight[d]):
            day_str += f" (Flight: {city_names[m[c[d-1]].as_long()]} -> {city_names[m[c[d]].as_long()]})"
        print(day_str)
    print("\nCity day counts:")
    for city in range(5):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")