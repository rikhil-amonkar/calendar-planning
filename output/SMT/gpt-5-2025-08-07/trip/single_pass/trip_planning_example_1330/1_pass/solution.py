# Solve the 25-day, 9-city itinerary with Z3, honoring direct-flight constraints
# and "day counts include flight days" rule. Prints JSON with an 'itinerary' list.

from z3 import *
import json

# Days are 1..25 (we'll index 0..24 in code)
N_DAYS = 25

cities = [
    "Salzburg",
    "Venice",
    "Bucharest",
    "Brussels",
    "Hamburg",
    "Copenhagen",
    "Nice",
    "Zurich",
    "Naples",
]
idx = {c: i for i, c in enumerate(cities)}

# Desired total presence days per city (counts include flight-day double counting)
target_days = {
    "Salzburg": 2,
    "Venice": 5,
    "Bucharest": 4,
    "Brussels": 2,
    "Hamburg": 4,
    "Copenhagen": 4,
    "Nice": 3,
    "Zurich": 5,
    "Naples": 4,
}

# Direct flights (bidirectional)
edges_raw = [
    ("Zurich", "Brussels"),
    ("Bucharest", "Copenhagen"),
    ("Venice", "Brussels"),
    ("Nice", "Zurich"),
    ("Hamburg", "Nice"),
    ("Zurich", "Naples"),
    ("Hamburg", "Bucharest"),
    ("Zurich", "Copenhagen"),
    ("Bucharest", "Brussels"),
    ("Hamburg", "Brussels"),
    ("Venice", "Naples"),
    ("Venice", "Copenhagen"),
    ("Bucharest", "Naples"),
    ("Hamburg", "Copenhagen"),
    ("Venice", "Zurich"),
    ("Nice", "Brussels"),
    ("Hamburg", "Venice"),
    ("Copenhagen", "Naples"),
    ("Nice", "Naples"),
    ("Hamburg", "Zurich"),
    ("Salzburg", "Hamburg"),
    ("Zurich", "Bucharest"),
    ("Brussels", "Naples"),
    ("Copenhagen", "Brussels"),
    ("Venice", "Nice"),
    ("Nice", "Copenhagen"),
]
edges = set()
for a, b in edges_raw:
    ai, bi = idx[a], idx[b]
    edges.add((ai, bi))
    edges.add((bi, ai))

# Z3 variables: city for each day (0..8)
city = [Int(f"city_{d+1}") for d in range(N_DAYS)]
s = Solver()

# Domain constraints
for d in range(N_DAYS):
    s.add(And(city[d] >= 0, city[d] < len(cities)))

# Direct flight or stay constraints between consecutive days
for d in range(1, N_DAYS):
    same = city[d] == city[d-1]
    direct = Or(*[And(city[d-1] == a, city[d] == b) for (a, b) in edges]) if edges else False
    s.add(Or(same, direct))

# Presence booleans: presence[c][d] is True if on day d (1-based) you are present in city c
# Rule: Day d counts for city[d] always, and also for city[d-1] if there is a flight on day d.
presence = {
    c: [Bool(f"present_{c}_{d+1}") for d in range(N_DAYS)]
    for c in range(len(cities))
}

for d in range(N_DAYS):
    for c in range(len(cities)):
        if d == 0:
            s.add(presence[c][d] == (city[d] == c))
        else:
            s.add(
                presence[c][d] ==
                Or(
                    city[d] == c,
                    And(city[d-1] == c, city[d] != city[d-1])  # departed from c on day d
                )
            )

# Enforce total presence days per city
for name, T in target_days.items():
    c = idx[name]
    s.add(Sum([If(presence[c][d], 1, 0) for d in range(N_DAYS)]) == T)

# Window constraints (presence-based, inclusive ranges):
# Nice between day 9 and day 11
for day in range(9, 12):  # 9..11
    s.add(presence[idx["Nice"]][day-1] == True)

# Copenhagen between day 18 and day 21
for day in range(18, 22):  # 18..21
    s.add(presence[idx["Copenhagen"]][day-1] == True)

# Naples between day 22 and day 25
for day in range(22, 26):  # 22..25
    s.add(presence[idx["Naples"]][day-1] == True)

# Meet friends at Brussels between day 21 and 22: require presence on both days to be safe
s.add(presence[idx["Brussels"]][21-1] == True)  # day 21
s.add(presence[idx["Brussels"]][22-1] == True)  # day 22

# Solve
if s.check() != sat:
    print(json.dumps({"itinerary": []}))
else:
    m = s.model()
    itinerary = []
    for d in range(N_DAYS):
        c_idx = m[city[d]].as_long()
        itinerary.append({"day": d+1, "city": cities[c_idx]})
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))