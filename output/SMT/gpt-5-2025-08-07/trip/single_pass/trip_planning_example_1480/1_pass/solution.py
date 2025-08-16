# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

# Cities and indices
cities = [
    "Istanbul",   # 0
    "Vienna",     # 1
    "Riga",       # 2
    "Brussels",   # 3
    "Madrid",     # 4
    "Vilnius",    # 5
    "Venice",     # 6
    "Geneva",     # 7
    "Munich",     # 8
    "Reykjavik"   # 9
]
C = {name: i for i, name in enumerate(cities)}

# Directed flight adjacency
allowed = {i: set() for i in range(len(cities))}

def add_bidir(a, b):
    allowed[C[a]].add(C[b])
    allowed[C[b]].add(C[a])

def add_dir(fr, to):
    allowed[C[fr]].add(C[to])

# Add direct flights from the prompt
add_bidir("Munich", "Vienna")
add_bidir("Istanbul", "Brussels")
add_bidir("Vienna", "Vilnius")
add_bidir("Madrid", "Munich")
add_bidir("Venice", "Brussels")
add_bidir("Riga", "Brussels")
add_bidir("Geneva", "Istanbul")
add_bidir("Munich", "Reykjavik")
add_bidir("Vienna", "Istanbul")
add_bidir("Riga", "Istanbul")
add_bidir("Reykjavik", "Vienna")
add_bidir("Venice", "Munich")
add_bidir("Madrid", "Venice")
add_bidir("Vilnius", "Istanbul")
add_bidir("Venice", "Vienna")
add_bidir("Venice", "Istanbul")
add_dir("Reykjavik", "Madrid")
add_dir("Riga", "Munich")
add_bidir("Munich", "Istanbul")
add_bidir("Reykjavik", "Brussels")
add_bidir("Vilnius", "Brussels")
add_dir("Vilnius", "Munich")
add_bidir("Madrid", "Vienna")
add_bidir("Vienna", "Riga")
add_bidir("Geneva", "Vienna")
add_bidir("Madrid", "Brussels")
add_bidir("Vienna", "Brussels")
add_bidir("Geneva", "Brussels")
add_bidir("Geneva", "Madrid")
add_bidir("Munich", "Brussels")
add_bidir("Madrid", "Istanbul")
add_bidir("Geneva", "Munich")
add_dir("Riga", "Vilnius")

days = range(1, 28)  # 1..27

# Variables: loc[d] is the city index for day d (the city you are "in" on that day)
loc = {d: Int(f"loc_{d}") for d in days}

# change[d] indicates a flight occurs on day d (only meaningful for d>=2)
change = {d: Bool(f"chg_{d}") for d in days}

s = Solver()

# Domain constraints
for d in days:
    s.add(And(loc[d] >= 0, loc[d] < len(cities)))

# Define change[d]: whether a flight occurs on day d (d>=2). For d==1, no flight.
s.add(change[1] == False)
for d in range(2, 28):
    s.add(change[d] == (loc[d] != loc[d-1]))

# Adjacency constraints: if a change happens, it must be along an allowed direct flight
for d in range(2, 28):
    # Either no change, or the (prev, curr) pair is allowed
    ors = [loc[d] == loc[d-1]]
    # Add Or over allowed pairs
    # Build disjuncts And(loc[d-1]==src, loc[d]==dst) for all allowed pairs
    pair_ors = []
    for src in range(len(cities)):
        if allowed[src]:
            pair_ors.extend([And(loc[d-1] == src, loc[d] == dst) for dst in allowed[src]])
    ors.append(Or(*pair_ors))
    s.add(Or(*ors))

# is_in[c][d] is True if you are "in" city c on day d under the counting rule:
# - On day 1: loc[1] == c
# - For day d>=2: (loc[d] == c) OR (change[d] and loc[d-1] == c)
is_in = {c: {d: Bool(f"in_{c}_{d}") for d in days} for c in range(len(cities))}

for c in range(len(cities)):
    # day 1
    s.add(is_in[c][1] == (loc[1] == c))
    # days 2..27
    for d in range(2, 28):
        s.add(is_in[c][d] == Or(loc[d] == c, And(change[d], loc[d-1] == c)))

# Duration requirements
required_days = {
    C["Istanbul"]: 4,
    C["Vienna"]: 4,
    C["Riga"]: 2,
    C["Brussels"]: 2,
    C["Madrid"]: 4,
    C["Vilnius"]: 4,
    C["Venice"]: 5,
    C["Geneva"]: 4,
    C["Munich"]: 5,
    C["Reykjavik"]: 2
}

for c, k in required_days.items():
    s.add(Sum([If(is_in[c][d], 1, 0) for d in days]) == k)

# Total flights implied by durations: sum(required) = 36, total days = 27 => flights = 9
s.add(Sum([If(change[d], 1, 0) for d in range(2, 28)]) == 9)

# Interval constraints (must be "in" these cities on these days)
# Geneva between day 1 and day 4
for d in range(1, 5):
    s.add(is_in[C["Geneva"]][d] == True)

# Venice workshop between day 7 and day 11
for d in range(7, 12):
    s.add(is_in[C["Venice"]][d] == True)

# Vilnius between day 20 and day 23
for d in range(20, 24):
    s.add(is_in[C["Vilnius"]][d] == True)

# Brussels wedding between day 26 and day 27
for d in range(26, 28):
    s.add(is_in[C["Brussels"]][d] == True)

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found with the given constraints.")

m = s.model()

# Build the JSON itinerary: day -> place (use loc[d])
itinerary = []
for d in days:
    city_idx = m.eval(loc[d]).as_long()
    itinerary.append({"day": d, "place": cities[city_idx]})

print(json.dumps({"itinerary": itinerary}, indent=2))