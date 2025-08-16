# Solve the 28-day, 10-city itinerary with flight-day double counting using Z3
# and output a JSON-formatted dictionary with the itinerary.

from z3 import *
import json

# Cities
cities = [
    "London", "Hamburg", "Reykjavik", "Barcelona", "Stuttgart",
    "Stockholm", "Zurich", "Milan", "Bucharest", "Tallinn"
]
city_to_idx = {c: i for i, c in enumerate(cities)}
idx_to_city = {i: c for c, i in city_to_idx.items()}

# Directed flight graph (include both directions for "A and B", only A->B for "from A to B")
edges_and = [
    ("London", "Hamburg"),
    ("London", "Reykjavik"),
    ("Milan", "Barcelona"),
    ("Reykjavik", "Barcelona"),
    ("Stockholm", "Reykjavik"),
    ("London", "Stuttgart"),
    ("Milan", "Zurich"),
    ("London", "Barcelona"),
    ("Stockholm", "Hamburg"),
    ("Zurich", "Barcelona"),
    ("Stockholm", "Stuttgart"),
    ("Milan", "Hamburg"),
    ("Stockholm", "Tallinn"),
    ("Hamburg", "Bucharest"),
    ("London", "Bucharest"),
    ("Milan", "Stockholm"),
    ("Stuttgart", "Hamburg"),
    ("London", "Zurich"),
    ("Milan", "Reykjavik"),
    ("London", "Stockholm"),
    ("Milan", "Stuttgart"),
    ("Stockholm", "Barcelona"),
    ("London", "Milan"),
    ("Zurich", "Hamburg"),
    ("Bucharest", "Barcelona"),
    ("Zurich", "Stockholm"),
    ("Barcelona", "Tallinn"),
    ("Zurich", "Tallinn"),
    ("Hamburg", "Barcelona"),
    ("Stuttgart", "Barcelona"),
    ("Zurich", "Reykjavik"),
    ("Zurich", "Bucharest"),
]
edges_from = [
    ("Reykjavik", "Stuttgart")
]

# Build allowed directed transitions as integer pairs
allowed = set()
for a, b in edges_and:
    ai, bi = city_to_idx[a], city_to_idx[b]
    allowed.add((ai, bi))
    allowed.add((bi, ai))
for a, b in edges_from:
    ai, bi = city_to_idx[a], city_to_idx[b]
    allowed.add((ai, bi))

# Required total presence days per city
required_days = {
    "Zurich": 2,
    "Bucharest": 2,
    "Hamburg": 5,
    "Barcelona": 4,
    "Reykjavik": 5,
    "Stuttgart": 5,
    "Stockholm": 2,
    "Tallinn": 4,
    "Milan": 5,
    "London": 3,
}
req = [required_days[c] for c in cities]

DAYS = 28
N = len(cities)

# Z3 variables
city = [Int(f"city_{d}") for d in range(1, DAYS + 1)]
present = [[Bool(f"present_{cities[c]}_{d}") for d in range(1, DAYS + 1)] for c in range(N)]

s = Solver()

# Domain for city variables
for d in range(DAYS):
    s.add(And(city[d] >= 0, city[d] < N))

# Flight constraints: If city changes between day d-1 and d (1-indexed), the transition must be allowed
for d in range(1, DAYS):  # transitions at day d+1 (1-indexed)
    # allow staying in same city OR moving along an allowed edge
    allowed_moves = [And(city[d - 1] == a, city[d] == b) for (a, b) in allowed]
    s.add(Or(city[d] == city[d - 1], Or(*allowed_moves)))

# Presence definition:
# present[c][d] is true if either:
#   - you are in city c on day d (city[d] == c), or
#   - you departed from city c on day d (i.e., day d >= 2, city[d-1] == c and city[d] != city[d-1])
for c in range(N):
    # Day 1
    s.add(present[c][0] == (city[0] == c))
    # Days 2..28
    for d in range(1, DAYS):
        s.add(present[c][d] == Or(city[d] == c, And(city[d - 1] == c, city[d] != city[d - 1])))

# Total presence days per city equals requirements
for c in range(N):
    s.add(Sum([If(present[c][d], 1, 0) for d in range(DAYS)]) == req[c])

# Special day constraints:
# London: must be present on days 1-3 (annual show)
for d in [1, 2, 3]:
    s.add(present[city_to_idx["London"]][d - 1])

# Milan: must be present on days 3-7 (meet friends in that window), which also fixes Milan's 5 days
for d in [3, 4, 5, 6, 7]:
    s.add(present[city_to_idx["Milan"]][d - 1])

# Zurich: must attend conference on days 7 and 8
for d in [7, 8]:
    s.add(present[city_to_idx["Zurich"]][d - 1])

# Reykjavik: visit relatives between days 9 and 13 (inclusive)
for d in [9, 10, 11, 12, 13]:
    s.add(present[city_to_idx["Reykjavik"]][d - 1])

# Solve
if s.check() != sat:
    raise RuntimeError("No solution found under the given constraints.")

m = s.model()

itinerary = []
for d in range(1, DAYS + 1):
    cidx = m[city[d - 1]].as_long()
    itinerary.append({"day": d, "city": idx_to_city[cidx]})

# Optional: sanity checks (can be commented out)
def compute_presence(itin):
    # itin: list of ints (city indices)
    pres = {c: set() for c in range(N)}
    for d in range(DAYS):
        # in destination city on day d
        pres[itin[d]].add(d + 1)
        # if a flight occurred this day (from previous city), count origin also
        if d >= 1 and itin[d] != itin[d - 1]:
            pres[itin[d - 1]].add(d + 1)
    return pres

itin_idx = [m[city[d - 1]].as_long() for d in range(1, DAYS + 1)]
presence_days = compute_presence(itin_idx)

# Validate counts
for cname, needed in required_days.items():
    cidx = city_to_idx[cname]
    assert len(presence_days[cidx]) == needed, f"City {cname} has {len(presence_days[cidx])} days, expected {needed}"

# Validate special days
for d in [1, 2, 3]:
    assert d in presence_days[city_to_idx["London"]]
for d in [3, 4, 5, 6, 7]:
    assert d in presence_days[city_to_idx["Milan"]]
for d in [7, 8]:
    assert d in presence_days[city_to_idx["Zurich"]]
for d in [9, 10, 11, 12, 13]:
    assert d in presence_days[city_to_idx["Reykjavik"]]

# Validate direct flights for changes
for d in range(1, DAYS):
    a = itin_idx[d - 1]
    b = itin_idx[d]
    if a != b:
        assert (a, b) in allowed, f"Non-direct flight on day {d+1}: {idx_to_city[a]} -> {idx_to_city[b]}"

# Output JSON
print(json.dumps({"itinerary": itinerary}, indent=2))