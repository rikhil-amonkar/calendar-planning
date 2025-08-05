from z3 import *
import json

# Mapping of city names to indices
city_to_index = {
    "Venice": 0,
    "Reykjavik": 1,
    "Munich": 2,
    "Santorini": 3,
    "Manchester": 4,
    "Porto": 5,
    "Bucharest": 6,
    "Tallinn": 7,
    "Valencia": 8,
    "Vienna": 9
}

index_to_city = {v: k for k, v in city_to_index.items()}

durations = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]

# Define flight connections
connections = [
    ("Bucharest", "Manchester"),
    ("Munich", "Venice"),
    ("Santorini", "Manchester"),
    ("Vienna", "Reykjavik"),
    ("Venice", "Santorini"),
    ("Munich", "Porto"),
    ("Valencia", "Vienna"),
    ("Manchester", "Vienna"),
    ("Porto", "Vienna"),
    ("Venice", "Manchester"),
    ("Santorini", "Vienna"),
    ("Munich", "Manchester"),
    ("Munich", "Reykjavik"),
    ("Bucharest", "Valencia"),
    ("Venice", "Vienna"),
    ("Bucharest", "Vienna"),
    ("Porto", "Manchester"),
    ("Munich", "Vienna"),
    ("Valencia", "Porto"),
    ("Munich", "Bucharest"),
    ("Tallinn", "Munich"),
    ("Santorini", "Bucharest"),
    ("Munich", "Valencia")
]

# Build allowed flight pairs
edge_set = set()
for conn in connections:
    cityA, cityB = conn
    i = city_to_index[cityA]
    j = city_to_index[cityB]
    edge_set.add((min(i, j), max(i, j)))

allowed_pairs = list(edge_set)
n = 10  # number of cities

# Z3 setup
s = Solver()

# Start and end days for each city
start = [Int(f'start_{i}') for i in range(n)]
end = [Int(f'end_{i}') for i in range(n)]

# Visit order variables
order = [Int(f'order_{k}') for k in range(n)]

# Duration constraints
for i in range(n):
    s.add(end[i] == start[i] + durations[i] - 1)
    s.add(start[i] >= 1)
    s.add(end[i] <= 24)

# Fixed start days
s.add(start[city_to_index["Munich"]] == 4)
s.add(start[city_to_index["Santorini"]] == 8)
s.add(start[city_to_index["Valencia"]] == 14)

# Order must be a permutation
s.add(Distinct(order))
for k in range(n):
    s.add(order[k] >= 0, order[k] < n)

# Chain constraints
for k in range(n-1):
    i = order[k]
    j = order[k+1]
    s.add(end[i] == start[j])

s.add(start[order[0]] == 1)
s.add(end[order[n-1]] == 24)

# Flight connections
for k in range(n-1):
    i = order[k]
    j = order[k+1]
    conds = []
    for pair in allowed_pairs:
        conds.append(And(i == pair[0], j == pair[1]))
        conds.append(And(i == pair[1], j == pair[0]))
    s.add(Or(conds))

# Solve
if s.check() == sat:
    model = s.model()
    # Extract order
    order_indices = [model.evaluate(order[k]).as_long() for k in range(n)]
    # Extract start/end days
    start_days = [model.evaluate(start[i]).as_long() for i in range(n)]
    end_days = [model.evaluate(end[i]).as_long() for i in range(n)]
    
    # Build day-by-day itinerary
    itinerary = []
    for day in range(1, 25):
        active_cities = []
        for i in range(n):
            if start_days[i] <= day <= end_days[i]:
                active_cities.append(index_to_city[i])
        active_cities.sort()
        place = active_cities if len(active_cities) > 1 else active_cities[0]
        itinerary.append({"day": day, "place": place})
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")