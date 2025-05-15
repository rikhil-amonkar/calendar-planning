from z3 import *

# City indices and day requirements:
# 0: Split      – required 5 days.
# 1: Vilnius    – required 4 days.
# 2: Santorini  – required 2 days; event: attend conference in Santorini on day 13 and day 14.
# 3: Madrid     – required 6 days.
city_names = ["Split", "Vilnius", "Santorini", "Madrid"]
required_credits = [5, 4, 2, 6]
# Total required credits = 5 + 4 + 2 + 6 = 17

# Total itinerary days:
DAYS = 14
# Credit rule:
#   Each day with no flight gives 1 credit for that day's city.
#   On a flight day (city change on that day) you get 1 credit for the departure and 1 for the arrival (i.e., 2 credits total).
# Therefore, total credits = DAYS + (# flight-days).
# To have 17 credits with 14 days, we need # flight-days = 17 - 14 = 3.
REQUIRED_FLIGHTS = 3

# Allowed direct flights (bidirectional unless specified otherwise):
# "Vilnius and Split"     : (1,0) and (0,1)
# "Split and Madrid"      : (0,3) and (3,0)
# "Madrid and Santorini"  : (3,2) and (2,3)
allowed_flights = [
    (1,0), (0,1),
    (0,3), (3,0),
    (3,2), (2,3)
]

# Create the Z3 solver
s = Solver()

# Variables:
# c[d] is the city (index) on day d, for d=0,...,DAYS-1.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean indicating if a flight occurs on day d.
# By convention, day 0 is not a flight day.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city must be one of the available ones.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, set flight indicator and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs on day d, the transition from c[d-1] to c[d] must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: returns an expression that's true if day d "includes" the target city.
# On a flight day, both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit for city c[0].
# For each day d >= 1:
#   - if no flight: add 1 credit for city c[d]
#   - if flight: add 1 credit for city c[d-1] (departure) and 1 for city c[d] (arrival).
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
    # Enforce required day credits.
    s.add(counts[city] == required_credits[city])
    # Enforce that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Conference in Santorini (city index 2) should be attended on day 13 and day 14.
# Days 13 and 14 correspond to indices 12 and 13.
s.add(inCityOnDay(12, 2))
s.add(inCityOnDay(13, 2))

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
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")