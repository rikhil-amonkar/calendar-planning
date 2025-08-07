import json
from z3 import *

# Define the cities and their indices
cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
city_index = {city: idx for idx, city in enumerate(cities)}

# Define the direct flight graph (undirected)
edges = [
    ("Reykjavik", "Stuttgart"),
    ("Stuttgart", "Split"),
    ("Stuttgart", "Vienna"),
    ("Prague", "Manchester"),
    ("Edinburgh", "Prague"),
    ("Manchester", "Split"),
    ("Prague", "Vienna"),
    ("Vienna", "Manchester"),
    ("Prague", "Split"),
    ("Vienna", "Lyon"),
    ("Stuttgart", "Edinburgh"),
    ("Split", "Lyon"),
    ("Stuttgart", "Manchester"),
    ("Prague", "Lyon"),
    ("Reykjavik", "Vienna"),
    ("Prague", "Reykjavik"),
    ("Vienna", "Split")
]

# Create directed edges (both directions for undirected graph)
directed_edges = []
for a, b in edges:
    directed_edges.append((city_index[a], city_index[b]))
    directed_edges.append((city_index[b], city_index[a]))

# Initialize Z3 solver
s = Solver()

# Define variables: current_city[0] to current_city[25]
current_city = [Int(f'current_city_{i}') for i in range(26)]
# Define fly flags for days 1 to 25
fly = [Bool(f'fly_{i}') for i in range(1, 26)]

# Constraint: current_city values are between 0 and 7
for i in range(26):
    s.add(current_city[i] >= 0, current_city[i] < 8)

# Constraints for each day from 1 to 25
for i in range(1, 26):
    # If not flying, stay in the same city
    s.add(Implies(Not(fly[i-1]), current_city[i] == current_city[i-1]))
    # If flying, the destination must be a direct flight neighbor
    s.add(Implies(fly[i-1], Or([And(current_city[i-1] == a, current_city[i] == b) for a, b in directed_edges])))

# Function to check if city c is visited on day i
def in_city(day, c):
    return Or(
        current_city[day-1] == c,
        And(fly[day-1], current_city[day] == c)
    )

# Total days per city constraints
required_days = [4, 3, 4, 5, 5, 2, 5, 4]  # Vienna, Lyon, Edinburgh, Reykjavik, Stuttgart, Manchester, Split, Prague
for c in range(8):
    total = 0
    for day in range(1, 26):
        total += If(in_city(day, c), 1, 0)
    s.add(total == required_days[c])

# Edinburgh must be visited on days 5-8
for day in range(1, 5):
    s.add(Not(in_city(day, city_index["Edinburgh"])))
for day in range(5, 9):
    s.add(in_city(day, city_index["Edinburgh"]))
for day in range(9, 26):
    s.add(Not(in_city(day, city_index["Edinburgh"])))

# Split must be visited at least once between days 19-23
s.add(Or([in_city(day, city_index["Split"]) for day in range(19, 24)]))

# Solve and output itinerary
if s.check() == sat:
    model = s.model()
    itinerary = []
    for day in range(1, 26):
        # Determine cities visited on this day
        start_city_val = model.eval(current_city[day-1]).as_long()
        start_city = cities[start_city_val]
        fly_today = model.eval(fly[day-1])
        places = [start_city]
        if is_true(fly_today):
            end_city_val = model.eval(current_city[day]).as_long()
            end_city = cities[end_city_val]
            if end_city != start_city:
                places.append(end_city)
        # Sort cities alphabetically for consistency
        places.sort()
        itinerary.append({"day": day, "place": places})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")