from z3 import *

# City indices and names:
# 0: Dublin   (3 days; event: meet friends between day 7 and day 9)
# 1: Madrid   (2 days; event: visit relatives between day 2 and day 3)
# 2: Oslo     (3 days)
# 3: London   (2 days)
# 4: Vilnius  (3 days)
# 5: Berlin   (5 days; event: wedding between day 3 and day 7)
city_names = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]

# Required day counts for each city.
req = [3, 2, 3, 2, 3, 5]

# Total required day contributions = 3+2+3+2+3+5 = 18.
# The trip has 13 base days. If f flights occur, then total contributions = 13 + f.
# To have 13 + f = 18, we require f = 5 flights.
# With 5 flight days there will be 6 segments (one per city), and these segments should be assigned distinct cities.

# Allowed direct flights (bidirectional unless specified otherwise):
allowed_flights = [
    # London and Madrid
    (3, 1), (1, 3),
    # Oslo and Vilnius
    (2, 4), (4, 2),
    # Berlin and Vilnius
    (5, 4), (4, 5),
    # Madrid and Oslo
    (1, 2), (2, 1),
    # Madrid and Dublin
    (1, 0), (0, 1),
    # London and Oslo
    (3, 2), (2, 3),
    # Madrid and Berlin
    (1, 5), (5, 1),
    # Berlin and Oslo
    (5, 2), (2, 5),
    # Dublin and Oslo
    (0, 2), (2, 0),
    # London and Dublin
    (3, 0), (0, 3),
    # London and Berlin
    (3, 5), (5, 3),
    # Berlin and Dublin
    (5, 0), (0, 5)
]

# Total itinerary days.
DAYS = 13

# Create Z3 variables.
# c[d] is the "base city" for day d (0-indexed for day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean flag (for d>=1) indicating that on day d a flight occurs (i.e. c[d] != c[d-1]).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is true if day d is the start of a segment (first day or when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be in {0,1,2,3,4,5}
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 6))

# Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# For days 1..DAYS-1, define flight indicators and constrain allowed flights.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then (c[d-1], c[d]) must be an allowed flight.
    s.add(Implies(flight[d], 
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Exactly 5 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 5)

# The cities that start each segment (i.e. day 0 and each day when a flight occurs) must all be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, ensure every city is visited at least once.
for city in range(6):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Now, compute the "day contributions" to each city's count.
# On day 0, the traveler contributes 1 (in city c[0]).
# For each day d from 1 to DAYS-1:
#   - If a flight occurs, add 1 for the departure city (c[d-1]) and 1 for the arrival city (c[d]).
#   - If no flight occurs, add 1 for the base city on that day.
counts = [Int(f"count_{city}") for city in range(6)]
for city in range(6):
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
# 1. Meet friends in Dublin (city 0) between day 7 and day 9.
friend_dublin = [inCityOnDay(d, 0) for d in range(6, 9)]
s.add(Or(friend_dublin))

# 2. Visit relatives in Madrid (city 1) between day 2 and day 3.
relatives_madrid = [inCityOnDay(d, 1) for d in [1, 2]]
s.add(Or(relatives_madrid))

# 3. Attend wedding in Berlin (city 5) between day 3 and day 7.
wedding_berlin = [inCityOnDay(d, 5) for d in range(2, 7)]
s.add(Or(wedding_berlin))

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
    for city in range(6):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")