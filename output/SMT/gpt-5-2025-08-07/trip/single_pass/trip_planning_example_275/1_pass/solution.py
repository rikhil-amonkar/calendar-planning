from z3 import Solver, Int, If, And, Or, Sum
import json

# Cities
VILNIUS, SPLIT, MADRID, SANTORINI = 0, 1, 2, 3
city_names = {VILNIUS: "Vilnius", SPLIT: "Split", MADRID: "Madrid", SANTORINI: "Santorini"}

# Days
DAYS = 14
days = list(range(1, DAYS + 1))

# Variables: city[d] is the city you are in at the end of day d (after any flight on day d)
city = {d: Int(f"city_{d}") for d in days}

s = Solver()

# Domain constraints: each day must be one of the cities
for d in days:
    s.add(Or(city[d] == VILNIUS, city[d] == SPLIT, city[d] == MADRID, city[d] == SANTORINI))

# Direct flight constraints: If you change cities from day d-1 to day d, it must be a direct flight.
# Allowed direct pairs (undirected) are: (Vilnius, Split), (Split, Madrid), (Madrid, Santorini)
direct_pairs = {
    (VILNIUS, SPLIT), (SPLIT, VILNIUS),
    (SPLIT, MADRID), (MADRID, SPLIT),
    (MADRID, SANTORINI), (SANTORINI, MADRID)
}

for d in range(2, DAYS + 1):
    s.add(Or(
        city[d] == city[d - 1],  # no flight (stay)
        Or(*[And(city[d - 1] == a, city[d] == b) for (a, b) in direct_pairs])  # direct flight
    ))

# Conference constraint: must be in Santorini on day 13 and 14
s.add(city[13] == SANTORINI)
s.add(city[14] == SANTORINI)

# Counting days with the "flight day counts for both cities" rule:
# For each city x, total_days[x] = sum_{d} [city[d] == x] + sum_{d=2..D} [city[d-1]==x and city[d]!=x]
def city_count(x):
    base_days = Sum([If(city[d] == x, 1, 0) for d in days])
    depart_bonus = Sum([If(And(city[d - 1] == x, city[d] != x), 1, 0) for d in range(2, DAYS + 1)])
    return base_days + depart_bonus

# Desired visit durations
s.add(city_count(SPLIT) == 5)
s.add(city_count(VILNIUS) == 4)
s.add(city_count(SANTORINI) == 2)
s.add(city_count(MADRID) == 6)

# Solve
if s.check() != 1:
    raise RuntimeError("No solution found")

m = s.model()

# Build itinerary: list of {"day": d, "city": name}
itinerary = [{"day": d, "city": city_names[m[city[d]].as_long()]} for d in days]

# Output JSON-formatted dictionary with 'itinerary'
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))