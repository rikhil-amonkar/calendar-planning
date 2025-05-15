from z3 import *

# City indices and requirements:
# 0: Salzburg  – required 4 days.
# 1: Stockholm – required 2 days.
# 2: Venice    – required 5 days; event: attend annual show in Venice from day 1 to day 5.
# 3: Frankfurt – required 4 days.
# 4: Florence  – required 4 days.
# 5: Barcelona – required 2 days.
# 6: Stuttgart – required 3 days.
city_names = ["Salzburg", "Stockholm", "Venice", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
required_credits = [4, 2, 5, 4, 4, 2, 3]
# Total required credits = 4+2+5+4+4+2+3 = 24

# Total itinerary days:
DAYS = 18
# On a day without a flight you get 1 credit for that city's stay.
# On a flight day (when you change cities) you get 1 credit for the departure and 1 for the arrival.
# So total credits = DAYS + (# flight-days)
# To reach 24 credits, we require exactly (# flight-days) = 24 - 18 = 6.
REQUIRED_FLIGHTS = 6

# Allowed direct flights (bidirectional):
# "Barcelona and Frankfurt"  : (5,3) and (3,5)
# "Florence and Frankfurt"   : (4,3) and (3,4)
# "Stockholm and Barcelona"  : (1,5) and (5,1)
# "Barcelona and Florence"   : (5,4) and (4,5)
# "Venice and Barcelona"     : (2,5) and (5,2)
# "Stuttgart and Barcelona"  : (6,5) and (5,6)
# "Frankfurt and Salzburg"   : (3,0) and (0,3)
# "Stockholm and Frankfurt"  : (1,3) and (3,1)
# "Stuttgart and Stockholm"  : (6,1) and (1,6)
# "Stuttgart and Frankfurt"  : (6,3) and (3,6)
# "Venice and Stuttgart"     : (2,6) and (6,2)
# "Venice and Frankfurt"     : (2,3) and (3,2)
allowed_flights = [
    (5, 3), (3, 5),
    (4, 3), (3, 4),
    (1, 5), (5, 1),
    (5, 4), (4, 5),
    (2, 5), (5, 2),
    (6, 5), (5, 6),
    (3, 0), (0, 3),
    (1, 3), (3, 1),
    (6, 1), (1, 6),
    (6, 3), (3, 6),
    (2, 6), (6, 2),
    (2, 3), (3, 2)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d] is the city (by index) you visit on day d (0-indexed: day0,..., day17).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that indicates whether a flight (i.e., a change of city) occurs on day d.
# By convention, day 0 is not a flight day.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city is one of the cities (0 to 6).
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, set flight indicator and enforce allowed transitions.
for d in range(1, DAYS):
    # Flight happens if today's city differs from yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, the (previous -> current) transition must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# This function returns a Boolean condition that holds true if on day d the city "target" is present.
# Note: On a flight day, day d is counted for both the departure (previous day) and arrival (current day).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city:
# Day 0 gives 1 credit for city c[0].
# For day d >= 1:
#   - if no flight: add 1 credit for city c[d].
#   - if there is a flight: add 1 credit for the departure city (c[d-1]) and 1 for the arrival city (c[d]).
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
    # Enforce the required day credit (stay days) for each city.
    s.add(counts[city] == required_credits[city])
    # Also ensure that every city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# Annual show in Venice (city index 2) from day 1 to day 5.
# These are days 1 to 5 corresponding to indices 0 through 4.
for d in range(0, 5):
    s.add(inCityOnDay(d, 2))

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