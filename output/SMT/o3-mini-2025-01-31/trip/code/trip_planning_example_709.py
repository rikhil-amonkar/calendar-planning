from z3 import *

# City indices and required day credits:
# 0: Helsinki   – required 4 days.
# 1: Valencia   – required 5 days.
# 2: Dubrovnik  – required 4 days.
# 3: Porto      – required 3 days; event: meet friend in Porto between day 16 and day 18.
# 4: Prague     – required 3 days.
# 5: Reykjavik  – required 4 days.
city_names = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
required_credits = [4, 5, 4, 3, 3, 4]
# Total required credits = 4+5+4+3+3+4 = 23

# Total itinerary days:
DAYS = 18
# Flight day rule:
#   - On a day without a flight you get 1 credit for that city.
#   - On a day with a flight (city change) you get 1 credit for the departure city and 1 for the arrival city.
# Total credits = DAYS + (# flight-days)
# To achieve 23 credits, we need (# flight-days) = 23 - 18 = 5.
REQUIRED_FLIGHTS = 5

# Allowed direct flights:
# Helsinki and Prague: (0,4) and (4,0)
# Prague and Valencia: (4,1) and (1,4)
# Valencia and Porto: (1,3) and (3,1)
# Helsinki and Reykjavik: (0,5) and (5,0)
# Dubrovnik and Helsinki: (2,0) and (0,2)
# Reykjavik and Prague: (5,4) and (4,5)
allowed_flights = [
    (0, 4), (4, 0),
    (4, 1), (1, 4),
    (1, 3), (3, 1),
    (0, 5), (5, 0),
    (2, 0), (0, 2),
    (5, 4), (4, 5)
]

s = Solver()

# Variables:
# c[d]: the city index on day d (0-indexed, for d from 0 to DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Boolean indicating whether a flight (city change) occurs on day d.
# Convention: on day 0 there is no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city index is between 0 and 5.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, define flight indicators and enforce allowed transitions.
for d in range(1, DAYS):
    # Flight happens if today's city is different from yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# On a flight day, day d "covers" both the departure (previous day) and arrival (current day).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city:
# Day 0 gives 1 credit for city c[0].
# For each day d>=1:
#    - if no flight: add 1 credit for city c[d],
#    - if flight: add 1 credit for the departure city (c[d-1]) and 1 credit for the arrival city (c[d]).
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
    # Also ensure every city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraint:
# Meet a friend in Porto (city 3) between day 16 and day 18.
# Days are 1-indexed in the statement, so day 16, 17, 18 correspond to indices 15, 16, 17.
s.add(Or(inCityOnDay(15, 3), inCityOnDay(16, 3), inCityOnDay(17, 3)))

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
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")