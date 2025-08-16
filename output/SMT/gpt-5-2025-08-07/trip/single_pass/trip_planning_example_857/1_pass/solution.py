# Solve the trip planning problem with Z3 and output a JSON itinerary.
# IMPORTANT: Flight day counts for BOTH cities (previous city and current city).

from z3 import *
import json

# Cities and indices
cities = [
    "Porto",
    "Geneva",
    "Mykonos",
    "Manchester",
    "Hamburg",
    "Naples",
    "Frankfurt",
]
city_to_idx = {c: i for i, c in enumerate(cities)}
P, G, M, MAN, H, N, F = (city_to_idx[c] for c in cities)

# Directed flight edges (include both directions for "A and B", one direction for "from A to B")
edges = set()
def add_bidirectional(a, b):
    edges.add((city_to_idx[a], city_to_idx[b]))
    edges.add((city_to_idx[b], city_to_idx[a]))
def add_directed(a, b):
    edges.add((city_to_idx[a], city_to_idx[b]))

add_bidirectional("Hamburg", "Frankfurt")
add_bidirectional("Naples", "Mykonos")
add_bidirectional("Hamburg", "Porto")
add_directed("Hamburg", "Geneva")  # directed only Hamburg -> Geneva
add_bidirectional("Mykonos", "Geneva")
add_bidirectional("Frankfurt", "Geneva")
add_bidirectional("Frankfurt", "Porto")
add_bidirectional("Geneva", "Porto")
add_bidirectional("Geneva", "Manchester")
add_bidirectional("Naples", "Manchester")
add_bidirectional("Frankfurt", "Naples")
add_bidirectional("Frankfurt", "Manchester")
add_bidirectional("Naples", "Geneva")
add_bidirectional("Porto", "Manchester")
add_bidirectional("Hamburg", "Manchester")

DAYS = 18

# Z3 variables: city per day (1..18); we index 0..17 in Python
city = [Int(f"city_{d+1}") for d in range(DAYS)]

s = Solver()

# Domain constraints
for d in range(DAYS):
    s.add(And(city[d] >= 0, city[d] < len(cities)))

# Flight constraints: If city changes from day d-1 to d, it must be a direct flight
for d in range(1, DAYS):
    # Either stay or transition along an allowed edge
    allowed_transitions = [And(city[d-1] == u, city[d] == v) for (u, v) in edges]
    s.add(Or(city[d] == city[d-1], Or(*allowed_transitions)))

# Helper: indicator (as Int 0/1) for condition
def I(cond):
    return If(cond, 1, 0)

# Counts with double-counting on departure day:
# For each city C:
# count(C) = sum_{d} [city[d]==C] + sum_{d=2..DAYS} [city[d-1]==C and city[d]!=city[d-1]]
def city_count(C):
    base = Sum([I(city[d] == C) for d in range(DAYS)])
    departures = Sum([I(And(city[d-1] == C, city[d] != city[d-1])) for d in range(1, DAYS)])
    return base + departures

# Desired day counts per city
desired = {
    P: 2,   # Porto
    G: 3,   # Geneva
    M: 3,   # Mykonos
    MAN: 4, # Manchester
    H: 5,   # Hamburg
    N: 5,   # Naples
    F: 2,   # Frankfurt
}
for C, v in desired.items():
    s.add(city_count(C) == v)

# Presence on a day for city C means:
# present(C, d) = (city[d]==C) OR (d>1 and city[d-1]==C and city[d]!=city[d-1])  [departure day]
def present(C, d_idx):  # d_idx is 0-based
    return Or(
        city[d_idx] == C,
        And(d_idx > 0, city[d_idx - 1] == C, city[d_idx] != city[d_idx - 1])
    )

# Frankfurt show on days 5 and 6 (1-based), i.e., indices 4 and 5
s.add(present(F, 4))
s.add(present(F, 5))

# Friend in Mykonos between day 10 and 12 (inclusive): at least one day present in Mykonos
s.add(Or(*[present(M, d-1) for d in range(10, 13)]))

# Wedding in Manchester between day 15 and 18 (inclusive): at least one day present in Manchester
s.add(Or(*[present(MAN, d-1) for d in range(15, 19)]))

# Ensure all seven cities are visited at least once (redundant given exact counts, but safe)
for C in range(len(cities)):
    s.add(city_count(C) >= 1)

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found under the given constraints.")

m = s.model()

# Build the itinerary as day-place mappings (no separate flight entries)
itinerary = []
for d in range(DAYS):
    c_idx = m[city[d]].as_long()
    itinerary.append({"day": d + 1, "place": cities[c_idx]})

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))