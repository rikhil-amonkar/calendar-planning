# Requires: z3-solver
# This program uses Z3 to construct a 15-day itinerary over 4 cities
# obeying the given stay lengths, mandatory presence windows, and direct-flight constraints.
from z3 import *
import json

# City indices
PARIS, MADRID, BUCHAREST, SEVILLE = 0, 1, 2, 3
CITY_NAMES = ["Paris", "Madrid", "Bucharest", "Seville"]
NUM_DAYS = 15
CITIES = [PARIS, MADRID, BUCHAREST, SEVILLE]

# Direct flight edges (undirected)
EDGES = [
    (PARIS, BUCHAREST),
    (SEVILLE, PARIS),
    (MADRID, BUCHAREST),
    (MADRID, PARIS),
    (MADRID, SEVILLE),
]

def edge_or_expr(a, b):
    # Returns a Z3 Or expression that is True iff (a,b) is a direct edge (undirected)
    return Or(*([And(a == i, b == j) for (i, j) in EDGES] +
                [And(a == j, b == i) for (i, j) in EDGES]))

# Z3 variables
main_city = [Int(f"main_{d}") for d in range(NUM_DAYS)]     # primary city for day d
is_flight = [Bool(f"flight_{d}") for d in range(NUM_DAYS)]  # whether day d is a flight day (present in two cities)
dest_city = [Int(f"dest_{d}") for d in range(NUM_DAYS)]     # if flight day, the other city present on day d

s = Solver()

# Domains and per-day constraints
for d in range(NUM_DAYS):
    s.add(And(main_city[d] >= 0, main_city[d] < 4))
    s.add(And(dest_city[d] >= 0, dest_city[d] < 4))

    # If flight day, must move between two distinct, directly connected cities
    s.add(Implies(is_flight[d],
                  And(dest_city[d] != main_city[d],
                      edge_or_expr(main_city[d], dest_city[d]))))
    # If not a flight day, 'dest' equals 'main' (so presence set is exactly one city)
    s.add(Implies(Not(is_flight[d]), dest_city[d] == main_city[d]))

# Continuity constraint: next day's main city equals today's main if no flight,
# otherwise equals today's dest if flight occurs today.
for d in range(NUM_DAYS - 1):
    s.add(main_city[d + 1] == If(is_flight[d], dest_city[d], main_city[d]))

# Exactly 3 flight days (since total stay tallies to 18 "city-days" and unique days are 15)
s.add(Sum([If(is_flight[d], 1, 0) for d in range(NUM_DAYS)]) == 3)

# Helper: presence of city c on day d
def present(d, c):
    return Or(main_city[d] == c, And(is_flight[d], dest_city[d] == c))

# Stay length constraints
def count_city_days(c):
    return Sum([If(main_city[d] == c, 1, 0) +
                If(And(is_flight[d], dest_city[d] == c), 1, 0)
                for d in range(NUM_DAYS)])

s.add(count_city_days(MADRID) == 7)
s.add(count_city_days(PARIS) == 6)
s.add(count_city_days(BUCHAREST) == 2)
s.add(count_city_days(SEVILLE) == 3)

# Mandatory windows:
# - Attend Madrid show on days 1..7 (inclusive)
for d in range(0, 7):
    s.add(present(d, MADRID))

# - Visit relatives in Bucharest between day 14 and day 15 (inclusive)
s.add(present(13, BUCHAREST))  # day 14 (0-based)
s.add(present(14, BUCHAREST))  # day 15 (0-based)

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found under the given constraints.")

m = s.model()

# Build itinerary JSON: for each day, list all cities present that day (1 or 2)
itinerary = []
for d in range(NUM_DAYS):
    main_val = m[main_city[d]].as_long()
    flight_val = is_true(m[is_flight[d]])
    dest_val = m[dest_city[d]].as_long()
    day_cities = [CITY_NAMES[main_val]]
    if flight_val and dest_val != main_val:
        day_cities.append(CITY_NAMES[dest_val])
    itinerary.append({"day": d + 1, "places": day_cities})

# Output JSON
print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))