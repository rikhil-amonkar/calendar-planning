from z3 import *

# City indices and required day credits:
# 0: Venice     – required 3 days; and must visit relatives in Venice between day 5 and day 7.
# 1: London     – required 3 days.
# 2: Lisbon     – required 4 days.
# 3: Brussels   – required 2 days; and you must attend a conference in Brussels on day 1 and day 2.
# 4: Reykjavik  – required 3 days.
# 5: Santorini  – required 3 days.
# 6: Madrid     – required 5 days; and you must attend a wedding in Madrid between day 7 and day 11.
city_names = ["Venice", "London", "Lisbon", "Brussels", "Reykjavik", "Santorini", "Madrid"]
required_credits = [3, 3, 4, 2, 3, 3, 5]
# Total required credits = 3+3+4+2+3+3+5 = 23

# Total itinerary days:
DAYS = 17
# Flight day rule:
# - On a day without a flight you get 1 credit for that day's city.
# - On a flight day (city change) you get 1 credit for the departure city and 1 for the arrival.
# Total credits = DAYS + (# flight-days)
# To achieve 23 credits, we require (# flight-days) = 23 - 17 = 6.
REQUIRED_FLIGHTS = 6

# Allowed direct flights (bidirectional unless stated otherwise):
# "Venice and Madrid"         : (0,6) and (6,0)
# "Lisbon and Reykjavik"      : (2,4) and (4,2)
# "Brussels and Venice"       : (3,0) and (0,3)
# "Venice and Santorini"      : (0,5) and (5,0)
# "Lisbon and Venice"         : (2,0) and (0,2)
# "from Reykjavik to Madrid"  : (4,6) only (unidirectional)
# "Brussels and London"       : (3,1) and (1,3)
# "Madrid and London"         : (6,1) and (1,6)
# "Santorini and London"      : (5,1) and (1,5)
# "London and Reykjavik"      : (1,4) and (4,1)
# "Brussels and Lisbon"       : (3,2) and (2,3)
# "Lisbon and London"         : (2,1) and (1,2)
# "Lisbon and Madrid"         : (2,6) and (6,2)
# "Madrid and Santorini"      : (6,5) and (5,6)
# "Brussels and Reykjavik"    : (3,4) and (4,3)
# "Brussels and Madrid"       : (3,6) and (6,3)
# "Venice and London"         : (0,1) and (1,0)
allowed_flights = [
    (0,6), (6,0),
    (2,4), (4,2),
    (3,0), (0,3),
    (0,5), (5,0),
    (2,0), (0,2),
    (4,6),          # unidirectional: Reykjavik -> Madrid
    (3,1), (1,3),
    (6,1), (1,6),
    (5,1), (1,5),
    (1,4), (4,1),
    (3,2), (2,3),
    (2,1), (1,2),
    (2,6), (6,2),
    (6,5), (5,6),
    (3,4), (4,3),
    (3,6), (6,3),
    (0,1), (1,0)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d]: the city index on day d (d = 0,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Boolean indicating if a flight (city change) occurs on day d.
# Convention: no flight on day 0.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each c[d] must be in {0,...,6}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, enforce flight indicator consistency and allowed flight transitions.
for d in range(1, DAYS):
    # A flight occurs if today’s city is different from yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper: on day d, inCityOnDay(d, target) is true if (on a non-flight day, c[d]==target) or 
# if a flight occurred, then either the departure (c[d-1]) or arrival (c[d]) equals target.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 grants 1 credit to city c[0]. For every day d>=1:
#   - if no flight: add 1 credit for city c[d]
#   - if flight: add 1 credit for departure (c[d-1]) and 1 for arrival (c[d]).
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily))
    # Enforce required day credits for each city.
    s.add(counts[city] == required_credits[city])
    # Ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Relatives in Venice between day 5 and day 7 (i.e. indices 4,5,6)
s.add(Or(inCityOnDay(4, 0), inCityOnDay(5, 0), inCityOnDay(6, 0)))

# 2. Conference in Brussels during day 1 and day 2 (i.e. indices 0 and 1 must be in Brussels)
s.add(inCityOnDay(0, 3))
s.add(inCityOnDay(1, 3))

# 3. Wedding in Madrid between day 7 and day 11 (i.e. indices 6,7,8,9,10)
s.add(Or(inCityOnDay(6, 6), inCityOnDay(7, 6), inCityOnDay(8, 6), inCityOnDay(9, 6), inCityOnDay(10, 6)))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city = m[c[d]].as_long()
        line = f"Day {d+1:02d}: {city_names[city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            line += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")