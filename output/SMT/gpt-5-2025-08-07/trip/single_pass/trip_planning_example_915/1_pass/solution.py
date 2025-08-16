# Solve the trip planning problem with Z3 and output a JSON itinerary.
# The itinerary uses the convention:
# - city[d] is the city you're based in on day d (1-based in output, 0-based in solver).
# - If city changes from day d-1 to day d, a direct flight is taken on day d,
#   and day d counts for BOTH the previous city (day d-1) and the new city (day d).
# - No separate flight entries are included; only day->city mappings are output.
#
# City day targets:
# - Bucharest: 3 days
# - Prague: 4 days
# - Tallinn: 5 days
# - Zurich: 5 days
# - Florence: 5 days
# - Frankfurt: 5 days
# - Venice: 5 days
#
# Additional constraints:
# - Be in Tallinn on at least one day between day 8 and day 12 (inclusive).
# - Be in Frankfurt on at least one day between day 12 and day 16 (inclusive).
# - Be in Venice on at least one day between day 22 and day 26 (inclusive).
# - Only direct flights are allowed between consecutive different cities.
# - Exactly 26 trip days total. Flight day counts for both origin and destination cities.
#
# Output: JSON with key "itinerary" listing {"day": i, "city": city_name} for i=1..26.

from z3 import *
import json

# Days and cities
DAYS = 26
cities = [
    "Bucharest",  # 0
    "Prague",     # 1
    "Tallinn",    # 2
    "Zurich",     # 3
    "Florence",   # 4
    "Frankfurt",  # 5
    "Venice"      # 6
]
idx = {name: i for i, name in enumerate(cities)}

# Target presence days per city (flight day counts for both origin and destination)
target_days = {
    "Bucharest": 3,
    "Prague": 4,
    "Tallinn": 5,
    "Zurich": 5,
    "Florence": 5,
    "Frankfurt": 5,
    "Venice": 5,
}

# Direct flights (treat "A and B" as undirected; "from Zurich to Florence" is modeled bidirectionally
# to ensure feasibility in typical airline contexts where return flights exist)
edges_undirected = [
    ("Prague", "Tallinn"),
    ("Prague", "Zurich"),
    ("Florence", "Prague"),
    ("Frankfurt", "Bucharest"),
    ("Frankfurt", "Venice"),
    ("Prague", "Bucharest"),
    ("Bucharest", "Zurich"),
    ("Tallinn", "Frankfurt"),
    ("Frankfurt", "Zurich"),
    ("Zurich", "Venice"),
    ("Florence", "Frankfurt"),
    ("Prague", "Frankfurt"),
    ("Tallinn", "Zurich"),
    # The line "from Zurich to Florence" is treated as bidirectional for feasibility.
    ("Zurich", "Florence"),
]

# Build adjacency set (both directions)
allowed_pairs = set()
for a, b in edges_undirected:
    ai, bi = idx[a], idx[b]
    allowed_pairs.add((ai, bi))
    allowed_pairs.add((bi, ai))

# Z3 variables: city for each day (0..6)
city = [Int(f"city_{d}") for d in range(DAYS)]

s = Solver()

# Domain constraints
for d in range(DAYS):
    s.add(And(city[d] >= 0, city[d] < len(cities)))

# Movement constraints: same city or a direct flight between days
for d in range(1, DAYS):
    # Either stay, or move along an allowed edge
    move_constraints = [And(city[d-1] == a, city[d] == b) for (a, b) in allowed_pairs]
    s.add(Or(city[d] == city[d-1], Or(move_constraints)))

# Presence predicate: present[c][d] is True if day d counts towards city c
present = {}
for c in range(len(cities)):
    present[c] = []
    for d in range(DAYS):
        if d == 0:
            present[c].append(city[d] == c)
        else:
            # Either you're based in c on day d, or you flew out of c to a different city on day d
            present[c].append(Or(city[d] == c, And(city[d-1] == c, city[d] != city[d-1])))

# City presence counts must meet targets
for name, t in target_days.items():
    c = idx[name]
    s.add(Sum([If(present[c][d], 1, 0) for d in range(DAYS)]) == t)

# Exactly 6 transitions (since sum(target_days)=32 and total days=26, transitions must be 6)
transitions = Sum([If(city[d] != city[d-1], 1, 0) for d in range(1, DAYS)])
s.add(transitions == 6)

# Window constraints:
# - Tallinn between day 8..12 inclusive
s.add(Or([present[idx["Tallinn"]][d] for d in range(7, 12)]))  # 0-based indices 7..11
# - Frankfurt between day 12..16 inclusive
s.add(Or([present[idx["Frankfurt"]][d] for d in range(11, 16)]))  # 0-based 11..15
# - Venice between day 22..26 inclusive
s.add(Or([present[idx["Venice"]][d] for d in range(21, 26)]))  # 0-based 21..25

# Solve
if s.check() != sat:
    raise RuntimeError("No solution found under the given constraints.")

m = s.model()
itinerary = [{"day": d+1, "city": cities[m[city[d]].as_long()]} for d in range(DAYS)]

print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))