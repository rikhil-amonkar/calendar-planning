# Requires: z3-solver
# This program finds a 22-day itinerary satisfying the constraints and prints it as JSON.

from z3 import *
import json

# City indices
cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
city_idx = {name: i for i, name in enumerate(cities)}
B, S, BU, R, L, T, LY = [city_idx[n] for n in cities]  # Berlin, Split, Bucharest, Riga, Lisbon, Tallinn, Lyon

# Allowed direct flights (pairs are directed)
edges = set()
def add_undirected(a, b):
    edges.add((a, b))
    edges.add((b, a))

def add_directed(a, b):
    edges.add((a, b))

# Add edges as per problem statement
add_undirected(L, BU)      # Lisbon <-> Bucharest
add_undirected(B, L)       # Berlin <-> Lisbon
add_undirected(BU, R)      # Bucharest <-> Riga
add_undirected(B, R)       # Berlin <-> Riga
add_undirected(S, LY)      # Split <-> Lyon
add_undirected(L, R)       # Lisbon <-> Riga
add_directed(R, T)         # Riga -> Tallinn (one-way)
add_undirected(B, S)       # Berlin <-> Split
add_undirected(LY, L)      # Lyon <-> Lisbon
add_undirected(B, T)       # Berlin <-> Tallinn
add_undirected(LY, BU)     # Lyon <-> Bucharest

DAYS = 22
N = DAYS

# Variables: city at end of each day (0..6)
city = [Int(f"city_{d+1}") for d in range(N)]

s = Solver()

# Domain constraints
for d in range(N):
    s.add(And(city[d] >= 0, city[d] < len(cities)))

# Flight feasibility: either stay in same city, or move along a direct flight
for d in range(1, N):
    allowed_moves = [And(city[d-1] == u, city[d] == v) for (u, v) in edges]
    s.add(Or(city[d] == city[d-1], Or(allowed_moves)))

# Helper: membership of being in city c on day d (counts flight-days for origin and destination)
def in_city_on_day(c, d_idx):
    # d_idx is 0-based
    if d_idx == 0:
        return city[0] == c
    else:
        return Or(city[d_idx] == c,
                  And(city[d_idx] != city[d_idx-1], city[d_idx-1] == c))

# Desired total counted days per city
desired = {
    B: 5,   # Berlin
    S: 3,   # Split
    BU: 3,  # Bucharest
    R: 5,   # Riga
    L: 3,   # Lisbon
    T: 4,   # Tallinn
    LY: 5   # Lyon
}

# Total count constraints per city
for c, need in desired.items():
    total = Sum([If(in_city_on_day(c, d), 1, 0) for d in range(N)])
    s.add(total == need)

# Window constraints (must be in these cities on these days)
# Days are 1-based in problem; convert to 0-based for indices.

# Berlin on days 1-5
for d in range(1, 6):
    s.add(in_city_on_day(B, d-1))

# Lyon on days 7-11
for d in range(7, 12):
    s.add(in_city_on_day(LY, d-1))

# Bucharest on days 13-15
for d in range(13, 16):
    s.add(in_city_on_day(BU, d-1))

# Exactly 6 flight days (S - D = 28 - 22 = 6)
flight_days = [If(city[d] != city[d-1], 1, 0) for d in range(1, N)]
s.add(Sum(flight_days) == 6)

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found.")
m = s.model()

# Build itinerary: for each day, report the end-of-day city (flight days count for both cities by rule)
itinerary = []
for d in range(N):
    c = m[city[d]].as_long()
    itinerary.append({"day": d+1, "city": cities[c]})

print(json.dumps({"itinerary": itinerary}, indent=2))