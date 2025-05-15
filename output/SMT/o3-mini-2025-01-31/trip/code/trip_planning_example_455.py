from z3 import *

# City indices:
# 0: Reykjavik – required 7 days.
# 1: Riga     – required 2 days; event: meet friend in Riga between day 1 and day 2.
# 2: Warsaw   – required 3 days.
# 3: Istanbul – required 6 days; event: attend wedding in Istanbul between day 2 and day 7.
# 4: Krakow   – required 7 days.
city_names = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
req = [7, 2, 3, 6, 7]  # Total required day credits = 7+2+3+6+7 = 25

# Total days in itinerary:
DAYS = 21
# Note: If no flight occurs on a day, that day gives 1 credit to the city.
# If a flight occurs on a day, say from A to B, then that day gives 1 credit to A and 1 credit to B.
# Thus, total credits = DAYS + (# of flight-days).
# We need 25 credits, so we require:
#      DAYS + F = 25  => 21 + F = 25  =>  F = 4
REQUIRED_FLIGHTS = 4

# Allowed direct flights: each pair is allowed in both directions.
allowed_flights = [
    # Istanbul and Krakow
    (3, 4), (4, 3),
    # Warsaw and Reykjavik
    (2, 0), (0, 2),
    # Istanbul and Warsaw
    (3, 2), (2, 3),
    # Riga and Istanbul
    (1, 3), (3, 1),
    # Krakow and Warsaw
    (4, 2), (2, 4),
    # Riga and Warsaw
    (1, 2), (2, 1)
]

# Create a Z3 solver instance.
s = Solver()

# Variables:
# c[d] is the "base" city on day d (0-indexed, days 0 to 20).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Bool variable that is True if a flight occurs on day d.
# (By construction, day 0 will have no flight.)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: c[d] must be one of the 0,...,4
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] <= 4)

# On day 0, no flight.
s.add(flight[0] == False)

# For days 1 to DAYS-1, define flight indicators:
for d in range(1, DAYS):
    # A flight occurs on day d exactly when the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If there is a flight on day d, then the transition must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# Returns an expression that is true if, on day d, the itinerary "includes" city 'target'.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    # On a flight day, the day counts for both the previous city and the current city.
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# On day 0, you get 1 credit for c[0].
# For each day d from 1 to DAYS-1:
#   - If no flight on d, add 1 credit for c[d].
#   - If flight on d, add 1 credit for c[d-1] and 1 credit for c[d].
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
    # Enforce that the computed credits equal the required credits.
    s.add(counts[city] == req[city])
    # Ensure that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:
# 1. Meet a friend in Riga between day 1 and day 2.
# Given day numbering starting with day 1 as index 0, we ensure that on at least one of day 1 or day 2 the itinerary includes Riga (city 1).
s.add(Or([inCityOnDay(d, 1) for d in [0, 1]]))

# 2. Attend a wedding in Istanbul between day 2 and day 7.
# That is, on at least one of days 2...7 (indices 1 through 6) the itinerary includes Istanbul (city 3).
s.add(Or([inCityOnDay(d, 3) for d in range(1, 7)]))

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