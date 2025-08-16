# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

# Cities
VAL, ATH, NAP, ZUR = 0, 1, 2, 3
city_names = {VAL: "Valencia", ATH: "Athens", NAP: "Naples", ZUR: "Zurich"}

days = 20

# Allowed direct flights (directed pairs)
allowed = set()
# "Valencia and Naples"
allowed.add((VAL, NAP)); allowed.add((NAP, VAL))
# "from Valencia to Athens"
allowed.add((VAL, ATH))
# "Athens and Naples"
allowed.add((ATH, NAP)); allowed.add((NAP, ATH))
# "Zurich and Naples"
allowed.add((ZUR, NAP)); allowed.add((NAP, ZUR))
# "Athens and Zurich"
allowed.add((ATH, ZUR)); allowed.add((ZUR, ATH))
# "Zurich and Valencia"
allowed.add((ZUR, VAL)); allowed.add((VAL, ZUR))

# Z3 variables: city on each day (the destination/where you are that day)
c = [Int(f"day_{d}") for d in range(1, days + 1)]

s = Solver()

# Domain constraints
for d in range(days):
    s.add(Or(c[d] == VAL, c[d] == ATH, c[d] == NAP, c[d] == ZUR))

# Flight adjacency constraints:
# If the city changes on day d (d>=2), it must be an allowed direct flight from day d-1 to day d.
for d in range(1, days):
    allowed_or = Or(*[And(c[d-1] == a, c[d] == b) for (a, b) in allowed]) if allowed else False
    s.add(Or(c[d] == c[d-1], allowed_or))

# Helper: presence in a city on a given day (counts flight days for both departure and arrival cities)
def present_in_city(city_val, d_idx):
    # d_idx is 1-based day index
    if d_idx == 1:
        return c[0] == city_val
    else:
        # Present if the itinerary shows the city that day,
        # or if we departed from that city that day (meaning previous day was the city and today is different).
        return Or(c[d_idx - 1] == city_val, And(c[d_idx - 2] == city_val, c[d_idx - 1] != city_val))

# City-day presence counts
def city_days(city_val):
    return Sum([If(present_in_city(city_val, d+1), 1, 0) for d in range(days)])

# Exact day requirements per city (including flight day double-counting)
s.add(city_days(VAL) == 6)  # Valencia
s.add(city_days(ATH) == 6)  # Athens
s.add(city_days(NAP) == 5)  # Naples
s.add(city_days(ZUR) == 6)  # Zurich

# "Visit relatives in Athens between day 1 and day 6" -> be present in Athens on each day 1..6
for d in range(1, 7):
    s.add(present_in_city(ATH, d))

# "Attend a wedding in Naples between day 16 and day 20" -> be present in Naples on each day 16..20
for d in range(16, 21):
    s.add(present_in_city(NAP, d))

# Since total requested presence days sum to 23 and the trip lasts 20 days,
# we expect exactly 3 flight days (each contributes one extra counted day).
flight_count = Sum([If(c[d] != c[d-1], 1, 0) for d in range(1, days)])
s.add(flight_count == 3)

if s.check() != sat:
    raise RuntimeError("No feasible itinerary found under the given constraints.")

m = s.model()

itinerary = []
for d in range(days):
    city = m.eval(c[d]).as_long()
    itinerary.append({"day": d + 1, "place": city_names[city]})

# Output JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))