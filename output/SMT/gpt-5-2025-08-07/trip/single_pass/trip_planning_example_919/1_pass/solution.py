from z3 import *
import json

# Cities
cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
city_to_idx = {name: i for i, name in enumerate(cities)}
n_days = 15

# Required total days per city (including flight-day overlap counts)
required_days = {
    "Vienna": 4,
    "Milan": 2,
    "Rome": 3,
    "Riga": 2,
    "Lisbon": 3,
    "Vilnius": 4,
    "Oslo": 3,
}

# Build allowed directed flight pairs
allowed_pairs = set()

def add_bidirectional(a, b):
    allowed_pairs.add((city_to_idx[a], city_to_idx[b]))
    allowed_pairs.add((city_to_idx[b], city_to_idx[a]))

def add_directed(a, b):
    allowed_pairs.add((city_to_idx[a], city_to_idx[b]))

# Given direct flights
add_bidirectional("Riga", "Oslo")
add_bidirectional("Rome", "Oslo")
add_bidirectional("Vienna", "Milan")
add_bidirectional("Vienna", "Vilnius")
add_bidirectional("Vienna", "Lisbon")
add_bidirectional("Riga", "Milan")
add_bidirectional("Lisbon", "Oslo")
add_directed("Rome", "Riga")
add_bidirectional("Rome", "Lisbon")
add_bidirectional("Vienna", "Riga")
add_bidirectional("Vienna", "Rome")
add_bidirectional("Milan", "Oslo")
add_bidirectional("Vienna", "Oslo")
add_bidirectional("Vilnius", "Oslo")
add_directed("Riga", "Vilnius")
add_bidirectional("Vilnius", "Milan")
add_bidirectional("Riga", "Lisbon")
add_bidirectional("Milan", "Lisbon")

allowed_pairs = list(allowed_pairs)

# Z3 variables
Ci = [Int(f"city_{d}") for d in range(1, n_days + 1)]  # destination city on day d
fly = [Bool(f"fly_{d}") for d in range(1, n_days + 1)]  # whether a flight happens on day d
P1 = Int("prev_day1_city")  # origin city for day 1 if a flight happens on day 1

s = Solver()

# Domain constraints for cities
for d in range(n_days):
    s.add(And(Ci[d] >= 0, Ci[d] < len(cities)))
s.add(And(P1 >= 0, P1 < len(cities)))

# Flight occurrence constraints:
# Day 1: fly_1 <=> (P1 != Ci[0])
s.add(fly[0] == (P1 != Ci[0]))

# Days 2..15: fly_d <=> (Ci[d-1] != Ci[d-2])
for d in range(2, n_days + 1):
    s.add(fly[d - 1] == (Ci[d - 1] != Ci[d - 2]))

# Direct flight constraints only when a flight happens
# Day 1 adjacency
s.add(Implies(
    fly[0],
    Or([And(P1 == a, Ci[0] == b) for (a, b) in allowed_pairs])
))

# Days 2..15 adjacency
for d in range(2, n_days + 1):
    s.add(Implies(
        fly[d - 1],
        Or([And(Ci[d - 2] == a, Ci[d - 1] == b) for (a, b) in allowed_pairs])
    ))

# Helper: presence on a given day in a given city (counts arrival city, and if a flight occurs, also the origin)
def present_on_day(day_idx, city_idx):
    # day_idx is 1-based
    if day_idx == 1:
        return Or(Ci[0] == city_idx, And(fly[0], P1 == city_idx))
    else:
        return Or(Ci[day_idx - 1] == city_idx, And(fly[day_idx - 1], Ci[day_idx - 2] == city_idx))

# Count total "days" per city including flight-day overlap
def total_days_for_city(city_idx):
    terms = []
    for d in range(1, n_days + 1):
        # Always count the destination city on day d
        terms.append(If(Ci[d - 1] == city_idx, 1, 0))
        # Also count the origin city if a flight occurs on day d
        if d == 1:
            terms.append(If(And(fly[0], P1 == city_idx), 1, 0))
        else:
            terms.append(If(And(fly[d - 1], Ci[d - 2] == city_idx), 1, 0))
    return Sum(terms)

# Enforce required total days per city
for name, req in required_days.items():
    s.add(total_days_for_city(city_to_idx[name]) == req)

# Additional constraints:
# - Must be present in Vienna on days 1 and 4 (conference days)
s.add(present_on_day(1, city_to_idx["Vienna"]))
s.add(present_on_day(4, city_to_idx["Vienna"]))

# - Must be present in Lisbon on days 11..13 (relatives visit)
for d in [11, 12, 13]:
    s.add(present_on_day(d, city_to_idx["Lisbon"]))

# - Must be present in Oslo on days 13..15 (friend meeting)
for d in [13, 14, 15]:
    s.add(present_on_day(d, city_to_idx["Oslo"]))

# Solve
if s.check() != sat:
    print(json.dumps({"error": "No feasible itinerary found"}, indent=2))
else:
    m = s.model()
    itinerary = []
    for d in range(1, n_days + 1):
        city_idx = m.evaluate(Ci[d - 1]).as_long()
        itinerary.append({"day": d, "city": cities[city_idx]})
    print(json.dumps({"itinerary": itinerary}, indent=2))