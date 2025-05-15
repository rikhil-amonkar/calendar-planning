from z3 import *

# City indices:
# 0: Amsterdam   – required 3 days; event: attend a workshop in Amsterdam between day 9 and day 11.
# 1: Vienna      – required 7 days.
# 2: Santorini   – required 4 days.
# 3: Lyon        – required 3 days; event: attend a wedding in Lyon between day 7 and day 9.
city_names = ["Amsterdam", "Vienna", "Santorini", "Lyon"]
required_credits = [3, 7, 4, 3]
# Total required credits = 3 + 7 + 4 + 3 = 17

# Total itinerary days:
DAYS = 14
# For counting credits:
# - A day with no flight gives 1 credit for that day’s city.
# - A day with a flight (i.e., when city changes from day (d-1) to d)
#   counts as 1 credit for the departure and 1 for the arrival.
# So total day credits = DAYS + (# flight-days).
# We need 17 credits, so number of flight-days must be 17 - 14 = 3.
REQUIRED_FLIGHTS = 3

# Allowed direct flights (bidirectional unless indicated otherwise):
# Vienna and Lyon: (1,3) and (3,1)
# Vienna and Santorini: (1,2) and (2,1)
# Vienna and Amsterdam: (1,0) and (0,1)
# Amsterdam and Santorini: (0,2) and (2,0)
# Lyon and Amsterdam: (3,0) and (0,3)
allowed_flights = [
    (1,3), (3,1),
    (1,2), (2,1),
    (1,0), (0,1),
    (0,2), (2,0),
    (3,0), (0,3)
]

# Create Z3 solver instance.
s = Solver()

# Variables:
# Let c[d] be the "base" city on day d (for days 0,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] indicates whether a flight occurs on day d.
# Convention: day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day d, c[d] is between 0 and len(city_names)-1.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

s.add(flight[0] == False)  # No flight on day 0.

# For each subsequent day, define flight occurrence and flight validity.
for d in range(1, DAYS):
    # A flight occurs on day d when the city differs from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the flight (from c[d-1] to c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: returns an expression that is true if on day d the itinerary "includes" the target city.
# Note: if a flight occurs on day d, then both the departure (c[d-1]) and the arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit for city c[0].
# For day d in 1...DAYS-1:
#   - if no flight: c[d] gets 1 credit.
#   - if flight: then c[d-1] gets 1 and c[d] gets 1 credit.
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
    # Each city's day credits must equal the required credits.
    s.add(counts[city] == required_credits[city])
    # And require that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Workshop in Amsterdam between day 9 and day 11.
# That means on at least one day among day 9, 10, or 11 (indices 8, 9, 10), the itinerary includes Amsterdam (city 0).
s.add(Or([inCityOnDay(d, 0) for d in range(8, 11)]))

# 2. Wedding in Lyon between day 7 and day 9.
# That means on at least one day among day 7, 8, or 9 (indices 6, 7, 8), the itinerary includes Lyon (city 3).
s.add(Or([inCityOnDay(d, 3) for d in range(6, 9)]))

# Solve the scheduling problem.
if s.check() == sat:
    model = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = model[c[d]].as_long()
        day_str = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and model.evaluate(flight[d]):
            dep = model[c[d-1]].as_long()
            arr = model[c[d]].as_long()
            day_str += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:12s}: {model.evaluate(counts[i])}")
else:
    print("No solution found.")