from z3 import *

# City indices:
# 0: Brussels   – required 2 days; event: attend conference on days 1 and 2.
# 1: Split      – required 5 days.
# 2: Barcelona  – required 7 days.
city_names = ["Brussels", "Split", "Barcelona"]
req = [2, 5, 7]  # Total required day credits = 2+5+7 = 14

# Total itinerary days:
DAYS = 12
# Credits: if no flight on a day, you get 1 credit for that city.
# If you fly on a day from city A to city B, that day gives 1 credit for A and 1 for B.
# Total credits = DAYS + (# flight days).
# We require 14 credits:
#   12 + F = 14, so F must be 2.
REQUIRED_FLIGHTS = 2

# Allowed flights:
# Brussels <-> Barcelona, and Barcelona <-> Split.
allowed_flights = [
    (0, 2), (2, 0),
    (2, 1), (1, 2)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d] is the "base" city on day d (with d = 0,...,11).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: Each day's city must be in {0,1,2}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# Day 0: No flight.
s.add(flight[0] == False)

# For days 1 through 11, define flight indicators.
for d in range(1, DAYS):
    # A flight occurs on day d if there is a change of city compared to day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs on day d, then the direct flight from day d-1 to day d must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days (among days 0..11).
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# This returns a condition that is True if on day d the itinerary "includes" the target city.
# On a flight day, both the departure (day d-1) and the arrival (day d) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# On day 0, you get 1 credit for city c[0].
# For each day d in 1..DAYS-1:
#   - If no flight on day d, add 1 credit for city c[d].
#   - If flight on day d, add 1 credit for c[d-1] AND 1 credit for c[d].
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    # Credit on day 0:
    base_credit = If(c[0] == city, 1, 0)
    daily_credits = []
    for d in range(1, DAYS):
        daily_credits.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base_credit + Sum(daily_credits))
    # Enforce required day credits for each city.
    s.add(counts[city] == req[city])
    # Ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:
# 1. Conference in Brussels on days 1 and 2.
# We require that on day 1 (index 0) and day 2 (index 1) the itinerary includes Brussels (city 0).
s.add(inCityOnDay(0, 0))
s.add(inCityOnDay(1, 0))

# Solve the model.
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