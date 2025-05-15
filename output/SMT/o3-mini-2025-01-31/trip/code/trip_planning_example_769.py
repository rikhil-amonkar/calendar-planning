from z3 import *

# City indices:
# 0: Porto       – required 5 days
# 1: Prague      – required 4 days
# 2: Reykjavik   – required 4 days; event: attend wedding in Reykjavik between day 4 and day 7.
# 3: Santorini   – required 2 days
# 4: Amsterdam   – required 2 days; event: attend conference in Amsterdam during day 14 and day 15.
# 5: Munich      – required 4 days; event: meet a friend in Munich between day 7 and day 10.
city_names = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
req = [5, 4, 4, 2, 2, 4]

# Total required day credits:
#   5 + 4 + 4 + 2 + 2 + 4 = 21
#
# In this itinerary:
# - When there is no flight on a day, that day contributes 1 credit.
# - When you take a flight on day X (i.e. the city changes from day X-1 to day X),
#   day X contributes 1 credit for the origin and 1 credit for the destination.
# For T days and F flight-days, total credits = T + F.
# Here T = 16, required total credits = 21, so we need F = 5 flight-days.
DAYS = 16
REQUIRED_FLIGHTS = 5

# Allowed direct flights (bidirectional unless stated otherwise):
allowed_flights = [
    # Porto <-> Amsterdam
    (0, 4), (4, 0),
    # Munich <-> Amsterdam
    (5, 4), (4, 5),
    # Reykjavik <-> Amsterdam
    (2, 4), (4, 2),
    # Munich <-> Porto
    (5, 0), (0, 5),
    # Prague <-> Reykjavik
    (1, 2), (2, 1),
    # Reykjavik <-> Munich
    (2, 5), (5, 2),
    # Amsterdam <-> Santorini
    (4, 3), (3, 4),
    # Prague <-> Amsterdam
    (1, 4), (4, 1),
    # Prague <-> Munich
    (1, 5), (5, 1)
]

# Create the Z3 solver
s = Solver()

# Variables:
# c[d] is the "base" city on day d (for d = 0,...,15)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable that indicates whether a flight occurs on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city must be in the range [0, 5]
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# Day 0 has no flight.
s.add(flight[0] == False)

# For each day d=1,...,DAYS-1, define flight existence and enforce allowed transitions.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))
    
# Constrain the total number of flight-days to equal REQUIRED_FLIGHTS (5)
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# This returns a condition that is true if, on day d, the itinerary "includes" city 'target'.
# On a day with a flight, both the departure city (previous day) and the arrival city count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# On day 0, the base city gets 1 credit.
# For each day d from 1 to DAYS-1:
#  - If no flight on day d, add 1 credit for the base city.
#  - If flight on day d, add 1 credit for both the departure (day d-1) and arrival (day d).
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base_credit = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base_credit + Sum(daily))
    # Enforce required credits for each city.
    s.add(counts[city] == req[city])
    # Also, ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Wedding in Reykjavik between day 4 and day 7.
#    That is, on at least one day among day 4 to day 7 (i.e. indices 3,4,5,6), the itinerary includes Reykjavik (city 2).
s.add(Or([inCityOnDay(d, 2) for d in range(3, 7)]))

# 2. Conference in Amsterdam during day 14 and day 15.
#    That is, on day 14 (index 13) and day 15 (index 14) the itinerary includes Amsterdam (city 4).
s.add(inCityOnDay(13, 4))
s.add(inCityOnDay(14, 4))

# 3. Meet a friend in Munich between day 7 and day 10.
#    That is, on at least one day among day 7 to day 10 (indices 6,7,8,9), the itinerary includes Munich (city 5).
s.add(Or([inCityOnDay(d, 5) for d in range(6, 10)]))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = city_idx
            day_str += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")