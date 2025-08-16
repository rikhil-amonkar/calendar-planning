# Requires: z3-solver (pip install z3-solver)
from z3 import *
import json

# Cities
HAMBURG = 0
MUNICH = 1
MANCHESTER = 2
LYON = 3
SPLIT = 4

city_names = {
    HAMBURG: "Hamburg",
    MUNICH: "Munich",
    MANCHESTER: "Manchester",
    LYON: "Lyon",
    SPLIT: "Split",
}

# Directed flight edges (include both directions for "A and B", and the one directed edge specified)
undirected_pairs = [
    (SPLIT, MUNICH),
    (MUNICH, MANCHESTER),
    (HAMBURG, MANCHESTER),
    (HAMBURG, MUNICH),
    (SPLIT, LYON),
    (LYON, MUNICH),
    (HAMBURG, SPLIT),
]
directed_only = [
    (MANCHESTER, SPLIT),
]

allowed_edges = set()
for a, b in undirected_pairs:
    allowed_edges.add((a, b))
    allowed_edges.add((b, a))
for a, b in directed_only:
    allowed_edges.add((a, b))

DAYS = 20
CITIES = [HAMBURG, MUNICH, MANCHESTER, LYON, SPLIT]

# Desired total days per city (counting overlap rules)
desired_days = {
    HAMBURG: 7,
    MUNICH: 6,
    MANCHESTER: 2,
    LYON: 2,
    SPLIT: 7,
}

s = Solver()

# City assignment per day: c[0] is Day 1, ..., c[19] is Day 20
c = [Int(f"c_{d+1}") for d in range(DAYS)]
for d in range(DAYS):
    s.add(Or([c[d] == k for k in CITIES]))

# Flight adjacency constraint: if change city from day d-1 to d, it must be a direct flight
for d in range(1, DAYS):
    same = c[d] == c[d-1]
    allowed_switch = Or([And(c[d-1] == a, c[d] == b) for (a, b) in allowed_edges])
    s.add(Or(same, allowed_switch))

# present[city][day] is True if that city counts the day according to overlap rule:
# If day t has c[t] == city => counts
# Also, if t > 1 and c[t-1] == city and c[t] != c[t-1] => counts (flight day counts for previous city)
present = {
    city: [Bool(f"present_{city_names[city]}_{d+1}") for d in range(DAYS)]
    for city in CITIES
}

for city in CITIES:
    for d in range(DAYS):
        if d == 0:
            s.add(present[city][d] == (c[d] == city))
        else:
            s.add(
                present[city][d] ==
                Or(
                    c[d] == city,
                    And(c[d-1] == city, c[d] != c[d-1])
                )
            )

# Exact day counts per city
for city in CITIES:
    s.add(Sum([If(present[city][d], 1, 0) for d in range(DAYS)]) == desired_days[city])

# Event constraints:
# - You want to attend the show in Lyon on Day 13 and Day 14 (days are 1-indexed).
#   That means Lyon must count for those days (either assigned that day, or departing from Lyon on that day).
s.add(present[LYON][12] == True)  # Day 13
s.add(present[LYON][13] == True)  # Day 14

# - You plan to visit relatives in Manchester between Day 19 and Day 20 (inclusive).
#   That means Manchester must count for Day 19 and Day 20.
s.add(present[MANCHESTER][18] == True)  # Day 19
s.add(present[MANCHESTER][19] == True)  # Day 20

# To produce a clearer itinerary, also pin specific days commonly implied by the constraints:
# Make Day 13 be Lyon explicitly (consistent with having Lyon count on Day 13-14 and total of 2 days in Lyon).
s.add(c[12] == LYON)
# Make Days 19-20 explicitly in Manchester (consistent with exactly 2 Manchester days and the relatives visit).
s.add(c[18] == MANCHESTER)
s.add(c[19] == MANCHESTER)

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found under the given constraints.")

m = s.model()

# Build itinerary JSON
itinerary = []
for d in range(DAYS):
    city = m.eval(c[d]).as_long()
    itinerary.append({"day": d + 1, "place": city_names[city]})

print(json.dumps({"itinerary": itinerary}, indent=2))