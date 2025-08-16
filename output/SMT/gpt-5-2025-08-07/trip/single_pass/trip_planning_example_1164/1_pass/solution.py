from z3 import *
import json

# Cities and required durations (days)
cities = [
    "Reykjavik",
    "Stockholm",
    "Porto",
    "Nice",
    "Venice",
    "Vienna",
    "Split",
    "Copenhagen",
]
idx = {c: i for i, c in enumerate(cities)}
dur_req = {
    "Reykjavik": 2,
    "Stockholm": 2,
    "Porto": 5,
    "Nice": 3,
    "Venice": 4,
    "Vienna": 3,
    "Split": 3,
    "Copenhagen": 2,
}
dur_list = [dur_req[c] for c in cities]

# Direct flights (undirected)
direct_pairs = [
    ("Copenhagen", "Vienna"),
    ("Nice", "Stockholm"),
    ("Split", "Copenhagen"),
    ("Nice", "Reykjavik"),
    ("Nice", "Porto"),
    ("Reykjavik", "Vienna"),
    ("Stockholm", "Copenhagen"),
    ("Nice", "Venice"),
    ("Nice", "Vienna"),
    ("Reykjavik", "Copenhagen"),
    ("Nice", "Copenhagen"),
    ("Stockholm", "Vienna"),
    ("Venice", "Vienna"),
    ("Copenhagen", "Porto"),
    ("Reykjavik", "Stockholm"),
    ("Stockholm", "Split"),
    ("Split", "Vienna"),
    ("Copenhagen", "Venice"),
    ("Vienna", "Porto"),
]

# Build allowed adjacency set (both directions)
allowed_pairs = set()
for a, b in direct_pairs:
    allowed_pairs.add((idx[a], idx[b]))
    allowed_pairs.add((idx[b], idx[a]))
allowed_pairs = list(allowed_pairs)

# Z3 variables
n = 8
days_total = 17

order = [Int(f"order_{i}") for i in range(n)]  # permutation of city indices (0..7)
s = [Int(f"s_{i}") for i in range(n)]          # start day of segment i (inclusive)
e = [Int(f"e_{i}") for i in range(n)]          # end day of segment i (inclusive)

sol = Solver()

# order is a permutation of 0..7
for i in range(n):
    sol.add(And(order[i] >= 0, order[i] < n))
sol.add(Distinct(order))

# Day bounds and chaining with overlaps
for i in range(n):
    sol.add(And(s[i] >= 1, s[i] <= days_total))
    sol.add(And(e[i] >= 1, e[i] <= days_total))
    sol.add(e[i] >= s[i])

sol.add(s[0] == 1)
for i in range(n - 1):
    # Overlap day: the flight (transition) happens on day e[i] == s[i+1]
    sol.add(s[i + 1] == e[i])
# End exactly on day 17
sol.add(e[n - 1] == days_total)

# Helper to select duration by city at position i
def duration_at(pos):
    return Sum([If(order[pos] == j, dur_list[j], 0) for j in range(n)])

# Duration constraints per city block
for i in range(n):
    sol.add(e[i] - s[i] + 1 == duration_at(i))

# Direct flight constraints between consecutive city blocks
for i in range(n - 1):
    sol.add(Or([And(order[i] == a, order[i + 1] == b) for (a, b) in allowed_pairs]))

# Meeting/attendance window constraints (segment intersects window)
def city_intersects_window(city_name, a, b):
    ci = idx[city_name]
    return Or([And(order[i] == ci, s[i] <= b, e[i] >= a) for i in range(n)])

# Windows:
# Reykjavik meet between day 3 and 4
sol.add(city_intersects_window("Reykjavik", 3, 4))
# Stockholm meet between day 4 and 5
sol.add(city_intersects_window("Stockholm", 4, 5))
# Porto wedding between day 13 and 17
sol.add(city_intersects_window("Porto", 13, 17))
# Vienna workshop between day 11 and 13
sol.add(city_intersects_window("Vienna", 11, 13))

# Solve
if sol.check() != sat:
    raise RuntimeError("No feasible itinerary found with given constraints.")

m = sol.model()

# Extract solution
order_vals = [m.eval(order[i]).as_long() for i in range(n)]
s_vals = [m.eval(s[i]).as_long() for i in range(n)]
e_vals = [m.eval(e[i]).as_long() for i in range(n)]
seq_cities = [cities[order_vals[i]] for i in range(n)]

# Build day -> city mapping
# Choose the "later" city on overlap days (i.e., if day == s[k], assign to city k)
itinerary = []
for d in range(1, days_total + 1):
    # Find the greatest i such that s[i] <= d
    chosen_idx = 0
    for i in range(n):
        if d >= s_vals[i]:
            chosen_idx = i
        else:
            break
    # Safety: if somehow d > e[chosen_idx], fall back to earlier segment
    if d > e_vals[chosen_idx]:
        for i in range(chosen_idx - 1, -1, -1):
            if s_vals[i] <= d <= e_vals[i]:
                chosen_idx = i
                break
    itinerary.append({"day": d, "city": seq_cities[chosen_idx]})

# Output JSON
print(json.dumps({"itinerary": itinerary}, indent=2))