# Solve the itinerary planning problem with Z3 and output a JSON itinerary.
# Requirements:
# - 10 cities, 32 total days.
# - Only direct flights between cities on change days.
# - Flight day counts for BOTH departure (previous city) and arrival (current city).
# - Fixed stay lengths per city.
# - Must be present in specified cities during required day ranges (presence includes flight-day overlap).
# - Output: JSON with 'itinerary': list of {"day": i, "city": name} for i=1..32.

from z3 import *
import json

# Cities and indices
cities = [
    "Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw",
    "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"
]
idx = {name: i for i, name in enumerate(cities)}

# Desired durations (in presence-days)
durations = {
    "Bucharest": 2,
    "Krakow": 4,
    "Munich": 3,
    "Barcelona": 5,
    "Warsaw": 5,
    "Budapest": 5,
    "Stockholm": 2,
    "Riga": 5,
    "Edinburgh": 5,
    "Vienna": 5,
}

# Direct flights
adj = {i: set() for i in range(len(cities))}

def add_undir(a, b):
    ai, bi = idx[a], idx[b]
    adj[ai].add(bi)
    adj[bi].add(ai)

def add_dir(a, b):
    ai, bi = idx[a], idx[b]
    adj[ai].add(bi)

# Undirected edges ("A and B")
add_undir("Budapest", "Munich")
add_undir("Bucharest", "Riga")
add_undir("Munich", "Krakow")
add_undir("Munich", "Warsaw")
add_undir("Munich", "Bucharest")
add_undir("Edinburgh", "Stockholm")
add_undir("Barcelona", "Warsaw")
add_undir("Edinburgh", "Krakow")
add_undir("Barcelona", "Munich")
add_undir("Stockholm", "Krakow")
add_undir("Budapest", "Vienna")
add_undir("Barcelona", "Stockholm")
add_undir("Stockholm", "Munich")
add_undir("Edinburgh", "Budapest")
add_undir("Barcelona", "Riga")
add_undir("Edinburgh", "Barcelona")
add_undir("Vienna", "Riga")
add_undir("Barcelona", "Budapest")
add_undir("Bucharest", "Warsaw")
add_undir("Vienna", "Krakow")
add_undir("Edinburgh", "Munich")
add_undir("Barcelona", "Bucharest")
add_undir("Edinburgh", "Riga")
add_undir("Vienna", "Stockholm")
add_undir("Warsaw", "Krakow")
add_undir("Barcelona", "Krakow")
add_undir("Vienna", "Bucharest")
add_undir("Budapest", "Warsaw")
add_undir("Vienna", "Warsaw")
add_undir("Barcelona", "Vienna")
add_undir("Budapest", "Bucharest")
add_undir("Vienna", "Munich")
add_undir("Riga", "Warsaw")
add_undir("Stockholm", "Riga")
add_undir("Stockholm", "Warsaw")
# Directed edge ("from Riga to Munich")
add_dir("Riga", "Munich")

# Build list of all directed edges for constraints
edge_pairs = [(u, v) for u in adj for v in adj[u]]

days = 32
n = len(cities)

# Decision variables: city assigned for each day (1..32)
c = [Int(f"c_{d}") for d in range(1, days + 1)]

s = Solver()

# Domain constraints
for d in range(days):
    s.add(And(c[d] >= 0, c[d] < n))

# Flight adjacency constraints:
# If city changes between day d-1 and d (for d>=2), require a direct edge (c[d-1] -> c[d]).
for d in range(1, days):
    same = (c[d] == c[d-1])
    # Or any valid directed edge (u->v)
    edge_ok = Or(*[And(c[d-1] == u, c[d] == v) for (u, v) in edge_pairs]) if edge_pairs else False
    s.add(Or(same, edge_ok))

# Presence bits: presence[city][day] in {0,1}
presence = [[Int(f"pres_{city}_{day}") for day in range(1, days + 1)] for city in range(n)]

for ci in range(n):
    for d in range(1, days + 1):
        if d == 1:
            # Present on day 1 iff assigned city is ci
            s.add(presence[ci][d-1] == If(c[d-1] == ci, 1, 0))
        else:
            # Present on day d if:
            # - assigned city is ci on day d, OR
            # - we changed from ci on day d-1 to some other city on day d (flight day counts for previous city)
            s.add(presence[ci][d-1] == If(Or(c[d-1] == ci, And(c[d-2] == ci, c[d-1] != c[d-2])), 1, 0))

# Duration constraints per city
for name, dur in durations.items():
    ci = idx[name]
    s.add(Sum(presence[ci]) == dur)

# Required presence intervals (inclusive)
def require_presence(city_name, start_day, end_day):
    ci = idx[city_name]
    for d in range(start_day, end_day + 1):
        s.add(presence[ci][d-1] == 1)

# Attendance/meeting windows
require_presence("Edinburgh", 1, 5)     # Meet friend between day 1 and day 5
require_presence("Budapest", 9, 13)     # Annual show day 9-13
require_presence("Stockholm", 17, 18)   # Meet friends day 17-18
require_presence("Munich", 18, 20)      # Workshop day 18-20
require_presence("Warsaw", 25, 29)      # Conference day 25-29

# Solve
if s.check() != sat:
    raise RuntimeError("No solution found for the given constraints.")

m = s.model()

# Build JSON itinerary: one city per day
itinerary = []
for d in range(1, days + 1):
    city_idx = m.eval(c[d-1]).as_long()
    itinerary.append({"day": d, "city": cities[city_idx]})

print(json.dumps({"itinerary": itinerary}, indent=2))