from z3 import *

# City indices and required day credits:
# 0: Paris    – required 5 days.
# 1: Florence – required 3 days.
# 2: Vienna   – required 2 days; visit relatives in Vienna between day 19 and day 20.
# 3: Porto    – required 3 days; attend a workshop in Porto between day 1 and day 3.
# 4: Munich   – required 5 days.
# 5: Nice     – required 5 days.
# 6: Warsaw   – required 3 days; attend a wedding in Warsaw between day 13 and day 15.
city_names = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
required_credits = [5, 3, 2, 3, 5, 5, 3]
# Total required credits = 5+3+2+3+5+5+3 = 26

# Total itinerary days:
DAYS = 20
# Flight day rule:
# * On a day without a flight you get 1 credit for that day's city.
# * On a day when a flight occurs (i.e. city change), you get 1 credit for the departure and 1 for the arrival.
# Hence, total credits = DAYS + (# flight-days)
# To have 26 credits: (# flight-days) = 26 - 20 = 6.
REQUIRED_FLIGHTS = 6

# Allowed direct flights (using city indices).
# "Florence and Vienna"      : (1,2) and (2,1)
# "Paris and Warsaw"         : (0,6) and (6,0)
# "Munich and Vienna"        : (4,2) and (2,4)
# "Porto and Vienna"         : (3,2) and (2,3)
# "Warsaw and Vienna"        : (6,2) and (2,6)
# "from Florence to Munich"  : (1,4) only (unidirectional)
# "Munich and Warsaw"        : (4,6) and (6,4)
# "Munich and Nice"          : (4,5) and (5,4)
# "Paris and Florence"       : (0,1) and (1,0)
# "Warsaw and Nice"          : (6,5) and (5,6)
# "Porto and Munich"         : (3,4) and (4,3)
# "Porto and Nice"           : (3,5) and (5,3)
# "Paris and Vienna"         : (0,2) and (2,0)
# "Nice and Vienna"          : (5,2) and (2,5)
# "Porto and Paris"          : (3,0) and (0,3)
# "Paris and Nice"           : (0,5) and (5,0)
# "Paris and Munich"         : (0,4) and (4,0)
# "Porto and Warsaw"         : (3,6) and (6,3)
allowed_flights = [
    (1,2), (2,1),
    (0,6), (6,0),
    (4,2), (2,4),
    (3,2), (2,3),
    (6,2), (2,6),
    (1,4),            # Unidirectional: from Florence to Munich only.
    (4,6), (6,4),
    (4,5), (5,4),
    (0,1), (1,0),
    (6,5), (5,6),
    (3,4), (4,3),
    (3,5), (5,3),
    (0,2), (2,0),
    (5,2), (2,5),
    (3,0), (0,3),
    (0,5), (5,0),
    (0,4), (4,0),
    (3,6), (6,3)
]

s = Solver()

# Variables:
# c[d] represents the city index on day d (d = 0,1,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that indicates if a flight (city change) occurs on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each c[d] must be one of 0,...,6.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, enforce flight indicator and allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if today's city differs from yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the transition from c[d-1] to c[d] must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function:
# inCityOnDay(d, target): True if, on day d, the traveler is in target.
# On a flight day, the day's credits count for both departure (previous day's city) and arrival.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city:
# Day 0 gives 1 credit for the starting city.
# For each day d>=1:
#   - if there's no flight, add 1 credit for that day's city,
#   - if a flight occurs, add 1 credit for the departure (c[d-1]) and 1 for the arrival (c[d]).
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily_contrib = []
    for d in range(1, DAYS):
        daily_contrib.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily_contrib))
    # Enforce required day credits.
    s.add(counts[city] == required_credits[city])
    # Also ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Workshop in Porto between day 1 and day 3 (indices 0,1,2).
s.add(Or(inCityOnDay(0, 3), inCityOnDay(1, 3), inCityOnDay(2, 3)))

# 2. Wedding in Warsaw between day 13 and day 15 (indices 12,13,14).
s.add(Or(inCityOnDay(12, 6), inCityOnDay(13, 6), inCityOnDay(14, 6)))

# 3. Visit relatives in Vienna between day 19 and day 20 (indices 18,19).
s.add(Or(inCityOnDay(18, 2), inCityOnDay(19, 2)))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        info = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:8s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")