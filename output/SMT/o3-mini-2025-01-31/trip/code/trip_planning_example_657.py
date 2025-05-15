from z3 import *

# City indices and required credits:
# 0: Frankfurt   – required 4 days.
# 1: Manchester – required 4 days.
# 2: Valencia   – required 4 days.
# 3: Naples     – required 4 days.
# 4: Oslo       – required 3 days.
# 5: Vilnius    – required 2 days.
# Additionally:
# - From day 13 to day 16 (i.e. indices 12,13,14,15), you must be in Frankfurt (annual show).
# - Attend a wedding in Vilnius between day 12 and day 13 (i.e. at least one of day 12 or day 13 when in Vilnius).
city_names = ["Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"]
required_credits = [4, 4, 4, 4, 3, 2]  # total = 21 credits

# Total itinerary days:
DAYS = 16
# Flight day rule:
#  - On a day with no flight: you get 1 credit for that day's city.
#  - On a flight day (when city changes) you get 1 credit for the departure city and 1 for the arrival.
# Hence total credits = DAYS + (# flight-days)
# To hit 21 credits we require (# flight-days) = 21 - 16 = 5.
REQUIRED_FLIGHTS = 5

# Allowed direct flights (bidirectional):
# "Valencia and Frankfurt"    : (2,0) and (0,2)
# "Manchester and Frankfurt"  : (1,0) and (0,1)
# "Naples and Manchester"     : (3,1) and (1,3)
# "Naples and Frankfurt"      : (3,0) and (0,3)
# "Naples and Oslo"           : (3,4) and (4,3)
# "Oslo and Frankfurt"        : (4,0) and (0,4)
# "Vilnius and Frankfurt"     : (5,0) and (0,5)
# "Oslo and Vilnius"          : (4,5) and (5,4)
# "Manchester and Oslo"       : (1,4) and (4,1)
# "Valencia and Naples"       : (2,3) and (3,2)
allowed_flights = [
    (2, 0), (0, 2),
    (1, 0), (0, 1),
    (3, 1), (1, 3),
    (3, 0), (0, 3),
    (3, 4), (4, 3),
    (4, 0), (0, 4),
    (5, 0), (0, 5),
    (4, 5), (5, 4),
    (1, 4), (4, 1),
    (2, 3), (3, 2)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d] is the city index on day d, for d in 0,...,DAYS-1.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean indicating if a flight (city change) occurs on day d.
# Convention: on day 0, there's no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city must be between 0 and 5.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# Define flight relationships and allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if the city on day d is different from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# On a flight day the day "covers" both the departure and arrival cities.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits (contributions) for each city.
# Day 0 contributes 1 credit to the city c[0].
# For every day d >= 1:
#   - if no flight: add 1 credit for city c[d],
#   - if flight: add 1 credit each for the departure (c[d-1]) and arrival (c[d]).
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
    # Enforce the required day credits.
    s.add(counts[city] == required_credits[city])
    # Ensure every city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:
# 1. Annual show in Frankfurt from day 13 to day 16.
#    Days 13,14,15,16 are indices 12, 13, 14, 15.
for d in range(12, 16):
    s.add(inCityOnDay(d, 0))  # 0 is Frankfurt

# 2. Wedding in Vilnius between day 12 and day 13.
#    That is on day 12 or day 13, i.e. indices 11 or 12.
s.add(Or(inCityOnDay(11, 5), inCityOnDay(12, 5)))  # 5 is Vilnius

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_info = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")