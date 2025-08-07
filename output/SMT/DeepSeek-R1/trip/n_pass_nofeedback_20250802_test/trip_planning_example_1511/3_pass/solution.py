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

durations = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]  # in the order of city_to_index

# Define the direct flight connections as tuples of city names
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

# Build edge_set as unordered pairs (min(i,j), max(i,j))
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

# Arrays for start and end days of each city
start = [Int(f'start_{i}') for i in range(n)]
end = [Int(f'end_{i}') for i in range(n)]

# Order: list of 10 integers representing the sequence of cities
order = [Int(f'order_{k}') for k in range(n)]

# Define Z3 arrays for start and end days
start_arr = Array('start_arr', IntSort(), IntSort())
end_arr = Array('end_arr', IntSort(), IntSort())

# Duration constraints and linking arrays
for i in range(n):
    s.add(end[i] == start[i] + durations[i] - 1)
    s.add(start_arr[i] == start[i])
    s.add(end_arr[i] == end[i])
    s.add(start[i] >= 1)
    s.add(end[i] <= 24)

# Fixed start days
s.add(start[city_to_index["Munich"]] == 4)
s.add(start[city_to_index["Santorini"]] == 8)
s.add(start[city_to_index["Valencia"]] == 14)

# Order must be a permutation of [0, n-1]
s.add(Distinct(order))
for k in range(n):
    s.add(order[k] >= 0)
    s.add(order[k] < n)

# Chain constraints: first city starts at day 1, last ends at day 24, consecutive cities have matching end and start
s.add(start_arr[order[0]] == 1)
s.add(end_arr[order[n-1]] == 24)
for k in range(n-1):
    s.add(end_arr[order[k]] == start_arr[order[k+1]])

# Flight connection constraints for consecutive cities in the order
for k in range(n-1):
    i = order[k]
    j = order[k+1]
    conds = []
    for pair in allowed_pairs:
        conds.append(And(i == pair[0], j == pair[1]))
        conds.append(And(i == pair[1], j == pair[0]))
    s.add(Or(conds))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    # Extract the order as a list of integers
    order_indices = [model.evaluate(order[k]).as_long() for k in range(n)]
    # Extract start and end days for each city
    start_days = [model.evaluate(start[i]).as_long() for i in range(n)]
    end_days = [model.evaluate(end[i]).as_long() for i in range(n)]
    
    # Build itinerary for each day
    itinerary = []
    for d in range(1, 25):  # Days 1 to 24
        active_cities = []
        for i in range(n):
            s_day = start_days[i]
            e_day = end_days[i]
            if s_day <= d <= e_day:
                active_cities.append(index_to_city[i])
        # Sort active cities alphabetically for consistent output
        active_cities.sort()
        # If one city, output as string; else as list
        place = active_cities[0] if len(active_cities) == 1 else active_cities
        itinerary.append({"day": d, "place": place})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")