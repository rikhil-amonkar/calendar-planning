from z3 import *

# City indices and names:
# 0: Dublin     (5 days; event: annual show in Dublin from day 11 to day 15)
# 1: Krakow     (4 days)
# 2: Istanbul   (3 days; event: meet friend in Istanbul between day 9 and day 11)
# 3: Venice     (3 days)
# 4: Naples     (4 days)
# 5: Brussels   (2 days)
# 6: Mykonos    (4 days; event: visit relatives in Mykonos between day 1 and day 4)
# 7: Frankfurt  (3 days; event: meet friends at Frankfurt between day 15 and day 17)
city_names = ["Dublin", "Krakow", "Istanbul", "Venice", "Naples", "Brussels", "Mykonos", "Frankfurt"]

# Required day contributions for each city:
req = [5, 4, 3, 3, 4, 2, 4, 3]
# Total required contributions = 5+4+3+3+4+2+4+3 = 28.
# Base days = 21.
# Each flight day (with a flight) counts double (departure and arrival), so:
#   21 + (#flights) = 28  =>  #flights = 7.
# This means the itinerary is partitioned into 8 segments (one for each visited city).

# Allowed direct flights (note: most are bidirectional; "from Brussels to Frankfurt" is one-way):
allowed_flights = [
    # Dublin and Brussels
    (0, 5), (5, 0),
    # Mykonos and Naples
    (6, 4), (4, 6),
    # Venice and Istanbul
    (3, 2), (2, 3),
    # Frankfurt and Krakow
    (7, 1), (1, 7),
    # Naples and Dublin
    (4, 0), (0, 4),
    # Krakow and Brussels
    (1, 5), (5, 1),
    # Naples and Istanbul
    (4, 2), (2, 4),
    # Naples and Brussels
    (4, 5), (5, 4),
    # Istanbul and Frankfurt
    (2, 7), (7, 2),
    # from Brussels to Frankfurt (one-way)
    (5, 7),
    # Istanbul and Krakow
    (2, 1), (1, 2),
    # Istanbul and Brussels
    (2, 5), (5, 2),
    # Venice and Frankfurt
    (3, 7), (7, 3),
    # Naples and Frankfurt
    (4, 7), (7, 4),
    # Dublin and Krakow
    (0, 1), (1, 0),
    # Venice and Brussels
    (3, 5), (5, 3),
    # Naples and Venice
    (4, 3), (3, 4),
    # Istanbul and Dublin
    (2, 0), (0, 2),
    # Venice and Dublin
    (3, 0), (0, 3),
    # Dublin and Frankfurt
    (0, 7), (7, 0)
]

DAYS = 21  # Number of base days in the itinerary

# Create Z3 variables:
# c[d] represents the base city on day d (0-indexed: day d corresponds to day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable indicating that a flight occurs on day d (for d >= 1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates that day d is the start of a segment (day 0 always starts a segment)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day d, the base city must be one of the 8 cities (0 to 7).
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 8)

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1 to 20:
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, ensure that the flight route from day d-1 to day d is one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 7 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 7)

# Ensure that the starting city of each segment (day 0 and any day a flight is taken) is distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(8):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# - Day 0 contributes 1 to the city c[0].
# - For each day d from 1 to DAYS-1:
#    if a flight occurs, add 1 for the departure (c[d-1]) and 1 for the arrival (c[d]);
#    otherwise, add 1 for c[d] only.
counts = [Int(f"count_{city}") for city in range(8)]
for city in range(8):
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

# Helper function: inCityOnDay(d, target)
# Returns a Z3 constraint expressing that on day d the itinerary "includes" the target city.
# (If a flight occurs on day d, both the departure (c[d-1]) and arrival (c[d]) count.)
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Annual show in Dublin (city 0) from day 11 to day 15.
#    Days 11 to 15 correspond to indices 10, 11, 12, 13, 14.
annual_show_dublin = [inCityOnDay(d, 0) for d in [10, 11, 12, 13, 14]]
s.add(Or(annual_show_dublin))

# 2. Meet friend in Istanbul (city 2) between day 9 and day 11.
#    Days 9 to 11 correspond to indices 8, 9, 10.
meet_friend_istanbul = [inCityOnDay(d, 2) for d in [8, 9, 10]]
s.add(Or(meet_friend_istanbul))

# 3. Visit relatives in Mykonos (city 6) between day 1 and day 4.
#    Days 1 to 4 correspond to indices 0, 1, 2, 3.
relatives_mykonos = [inCityOnDay(d, 6) for d in [0, 1, 2, 3]]
s.add(Or(relatives_mykonos))

# 4. Meet friends at Frankfurt (city 7) between day 15 and day 17.
#    Days 15 to 17 correspond to indices 14, 15, 16.
friends_frankfurt = [inCityOnDay(d, 7) for d in [14, 15, 16]]
s.add(Or(friends_frankfurt))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base_city = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[base_city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base_city]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for i in range(8):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")