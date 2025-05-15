from z3 import *

# City indices:
# 0: Prague    – required 2 days.
# 1: Berlin    – required 3 days; event: attend conference in Berlin on day 6 and day 8.
# 2: Tallinn   – required 5 days; event: visit relatives in Tallinn between day 8 and day 12.
# 3: Stockholm – required 5 days.
city_names = ["Prague", "Berlin", "Tallinn", "Stockholm"]
req = [2, 3, 5, 5]  # Total required day credits = 2+3+5+5 = 15

# Total itinerary days.
DAYS = 12
# Note: When no flight occurs on a day, 1 credit is given for that city.
# If a flight occurs on a day (from city A to B), both A and B get 1 credit.
# Total credits = DAYS + (# flight-days). We require 15 credits:
#     12 + F = 15  => F = 3.
REQUIRED_FLIGHTS = 3

# Allowed direct flights (bidirectional unless stated otherwise):
allowed_flights = [
    # Berlin <-> Tallinn
    (1, 2), (2, 1),
    # Prague <-> Tallinn
    (0, 2), (2, 0),
    # Stockholm <-> Tallinn
    (3, 2), (2, 3),
    # Prague <-> Stockholm
    (0, 3), (3, 0),
    # Stockholm <-> Berlin
    (3, 1), (1, 3)
]

# Create Z3 solver
s = Solver()

# Variables:
# c[d] is the "base" city on day d (0-indexed, d=0,...,11).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Bool indicating whether a flight occurs on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints for each day.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# Day 0: no flight.
s.add(flight[0] == False)

# For days 1 to 11, a flight occurs if the city changes.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    # If there is a flight on day d, the flight must be allowed
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# This returns an expression that is True if on day d the itinerary "includes" the target city.
# On a flight day, both the departure (day d-1) and the arrival (day d) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# On day 0, the base city gets 1 credit.
# For each day d from 1 to DAYS-1:
#   - If no flight on day d, add 1 credit for city c[d].
#   - If a flight occurs on day d, add 1 credit for c[d-1] and 1 credit for c[d].
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
    # Enforce the required day credits.
    s.add(counts[city] == req[city])
    # Ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:
# 1. Attend conference in Berlin on day 6 and day 8.
# Assuming day numbering starts at 1, day6 -> index 5 and day8 -> index 7.
s.add(inCityOnDay(5, 1))
s.add(inCityOnDay(7, 1))

# 2. Visit relatives in Tallinn between day 8 and day 12.
# That is on at least one day among day 8 to day 12 (indices 7..11), the itinerary includes Tallinn (city 2).
s.add(Or([inCityOnDay(d, 2) for d in range(7, DAYS)]))

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
        print(f"{city_names[i]:9s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")