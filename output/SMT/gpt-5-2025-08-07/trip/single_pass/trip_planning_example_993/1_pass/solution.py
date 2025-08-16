# Solve the itinerary planning problem with Z3 and print a JSON itinerary.
# IMPORTANT: Flight days count for both departure and arrival cities.

from z3 import *
import json

# City indexing
cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
idx = {name: i for i, name in enumerate(cities)}
n_days = 15

# Required total days per city (including flight-day double counting)
required_days = {
    "Riga": 2,
    "Frankfurt": 3,
    "Amsterdam": 2,
    "Vilnius": 5,
    "London": 2,
    "Stockholm": 3,
    "Bucharest": 4,
}

# Direct flights (treat as undirected)
direct_pairs = [
    ("London", "Amsterdam"),
    ("Vilnius", "Frankfurt"),
    ("Riga", "Vilnius"),
    ("Riga", "Stockholm"),
    ("London", "Bucharest"),
    ("Amsterdam", "Stockholm"),
    ("Amsterdam", "Frankfurt"),
    ("Frankfurt", "Stockholm"),
    ("Bucharest", "Riga"),
    ("Amsterdam", "Riga"),
    ("Amsterdam", "Bucharest"),
    ("Riga", "Frankfurt"),
    ("Bucharest", "Frankfurt"),
    ("London", "Frankfurt"),
    ("London", "Stockholm"),
    ("Amsterdam", "Vilnius"),
]

# Build allowed transition pairs (including "stay" pairs)
allowed_transitions = set()
for a, b in direct_pairs:
    ia, ib = idx[a], idx[b]
    allowed_transitions.add((ia, ib))
    allowed_transitions.add((ib, ia))
for i in range(len(cities)):
    allowed_transitions.add((i, i))  # staying is always allowed

# Z3 variables: city for each day (1..15)
city = [Int(f"city_{d}") for d in range(1, n_days + 1)]
s = Solver()

# Domain constraints
for d in range(n_days):
    s.add(And(city[d] >= 0, city[d] < len(cities)))

# Transition constraints: each step must be staying or a direct flight
for d in range(1, n_days):  # day index d corresponds to day (d+1)
    s.add(Or(*[And(city[d-1] == i, city[d] == j) for (i, j) in allowed_transitions]))

# Helper: presence in a city on a given day, counting flight-day double presence
def present_expr(c_idx, day):  # day is 1-based
    cd = city[day - 1]
    if day == 1:
        return cd == c_idx
    prev_cd = city[day - 2]
    # Present if assigned to c on this day, or departed from c today (flight from prev_cd=c to cd!=c)
    return Or(cd == c_idx, And(prev_cd == c_idx, cd != prev_cd))

# Count constraints: total presence per city equals required_days
for cname, need in required_days.items():
    c = idx[cname]
    # Sum of assigned days
    assigned_sum = Sum([If(city[d] == c, 1, 0) for d in range(n_days)])
    # Sum of departure-day bonuses (days 2..15 where we leave this city)
    depart_sum = Sum([If(And(city[d - 1] == c, city[d] != city[d - 1]), 1, 0) for d in range(1, n_days)])
    s.add(assigned_sum + depart_sum == need)

# Event constraints using presence (flight days count as presence):
# - Meet friend in Amsterdam between day 2 and day 3 (inclusive)
s.add(Or(present_expr(idx["Amsterdam"], 2), present_expr(idx["Amsterdam"], 3)))
# - Attend workshop in Vilnius between day 7 and day 11 (inclusive)
s.add(Or(*[present_expr(idx["Vilnius"], d) for d in range(7, 12)]))
# - Attend wedding in Stockholm between day 13 and day 15 (inclusive)
s.add(Or(*[present_expr(idx["Stockholm"], d) for d in range(13, 16)]))

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found under the given constraints.")

m = s.model()

# Build the itinerary as a list of day-place mappings
itinerary = []
for d in range(1, n_days + 1):
    c_index = m[city[d - 1]].as_long()
    itinerary.append({"day": d, "city": cities[c_index]})

# Print JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))