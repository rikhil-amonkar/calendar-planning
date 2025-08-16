# Solve the trip planning problem with Z3 and output a JSON itinerary.
# Constraints:
# - 6 cities over 18 days
# - Only direct flights between allowed city pairs
# - Flight day counts for both departure and arrival cities
# - City stay targets (days counted with flight-double-count rule):
#     Helsinki: 4, Valencia: 5, Dubrovnik: 4, Porto: 3, Prague: 3, Reykjavik: 4
# - Meet a friend in Porto on at least one of days 16-18
# - Output a JSON dictionary with an 'itinerary' key: list of {day, place}

from z3 import *
import json

# Problem data
DAYS = 18
cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
idx = {c: i for i, c in enumerate(cities)}

# Targets: counted days per city (including flight-day double counting)
targets = {
    "Helsinki": 4,
    "Valencia": 5,
    "Dubrovnik": 4,
    "Porto": 3,
    "Prague": 3,
    "Reykjavik": 4,
}

# Allowed direct flights (undirected)
edges = [
    ("Helsinki", "Prague"),
    ("Prague", "Valencia"),
    ("Valencia", "Porto"),
    ("Helsinki", "Reykjavik"),
    ("Dubrovnik", "Helsinki"),
    ("Reykjavik", "Prague"),
]
# Build allowed transition pairs, including staying in the same city
allowed_pairs = set()
for a, b in edges:
    ia, ib = idx[a], idx[b]
    allowed_pairs.add((ia, ib))
    allowed_pairs.add((ib, ia))
for i in range(len(cities)):
    allowed_pairs.add((i, i))  # staying put is allowed

# Z3 variables: city per day (0..N-1)
N = len(cities)
c = [Int(f"c_{d+1}") for d in range(DAYS)]

s = Solver()

# Domain constraints
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < N))

# Transition constraints: if we change city from day d to d+1, it must be an allowed direct flight
for d in range(1, DAYS):
    # Enforce (c[d-1], c[d]) in allowed_pairs
    s.add(Or([And(c[d-1] == i, c[d] == j) for (i, j) in allowed_pairs]))

# Each city is visited at least once
for name, i in idx.items():
    s.add(Or([c[d] == i for d in range(DAYS)]))

# Porto friend meeting: at least one of days 16, 17, 18 is Porto
porto = idx["Porto"]
s.add(Or(c[15] == porto, c[16] == porto, c[17] == porto))

# Counted days per city: occurrences + number of leaving transitions = target
for name, i in idx.items():
    occ = Sum([If(c[d] == i, 1, 0) for d in range(DAYS)])
    leaves = Sum([If(And(c[d-1] == i, c[d] != i), 1, 0) for d in range(1, DAYS)])
    s.add(occ + leaves == targets[name])

# Solve
if s.check() != sat:
    raise RuntimeError("No valid itinerary found under the given constraints.")

m = s.model()

# Build itinerary JSON: list of day-place mappings
itinerary = [{"day": d + 1, "place": cities[m.evaluate(c[d]).as_long()]} for d in range(DAYS)]
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))