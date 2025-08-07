from z3 import *
import json

# City mapping and durations
city_to_index = {
    "Venice": 0, "Reykjavik": 1, "Munich": 2, "Santorini": 3,
    "Manchester": 4, "Porto": 5, "Bucharest": 6, "Tallinn": 7,
    "Valencia": 8, "Vienna": 9
}
index_to_city = {v: k for k, v in city_to_index.items()}
durations = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]

# Flight connections
connections = [
    ("Bucharest", "Manchester"), ("Munich", "Venice"), 
    ("Santorini", "Manchester"), ("Vienna", "Reykjavik"),
    ("Venice", "Santorini"), ("Munich", "Porto"),
    ("Valencia", "Vienna"), ("Manchester", "Vienna"),
    ("Porto", "Vienna"), ("Venice", "Manchester"),
    ("Santorini", "Vienna"), ("Munich", "Manchester"),
    ("Munich", "Reykjavik"), ("Bucharest", "Valencia"),
    ("Venice", "Vienna"), ("Bucharest", "Vienna"),
    ("Porto", "Manchester"), ("Munich", "Vienna"),
    ("Valencia", "Porto"), ("Munich", "Bucharest"),
    ("Tallinn", "Munich"), ("Santorini", "Bucharest"),
    ("Munich", "Valencia")
]

# Create allowed flight pairs
edge_set = set()
for cityA, cityB in connections:
    i, j = city_to_index[cityA], city_to_index[cityB]
    edge_set.add((min(i, j), max(i, j)))
allowed_pairs = list(edge_set)
n = 10  # Number of cities

# Initialize Z3 solver
s = Solver()

# Z3 arrays for start/end days
start_arr = Array('start_arr', IntSort(), IntSort())
end_arr = Array('end_arr', IntSort(), IntSort())

# Create variables for each city's start day
start_vars = [Int(f'start_{i}') for i in range(n)]
end_vars = [Int(f'end_{i}') for i in range(n)]

# Duration constraints
for i in range(n):
    s.add(end_arr[i] == start_arr[i] + durations[i] - 1)
    s.add(start_arr[i] == start_vars[i])
    s.add(end_arr[i] == end_vars[i])
    s.add(start_vars[i] >= 1, end_vars[i] <= 24)

# Fixed start dates
s.add(start_arr[city_to_index["Munich"]] == 4)
s.add(start_arr[city_to_index["Santorini"]] == 8)
s.add(start_arr[city_to_index["Valencia"]] == 14)

# Visit order variables
order = [Int(f'order_{k}') for k in range(n)]

# Order must be a permutation
s.add(Distinct(order))
for k in range(n):
    s.add(order[k] >= 0, order[k] < n)

# Chain constraints
s.add(start_arr[order[0]] == 1)
s.add(end_arr[order[n-1]] == 24)
for k in range(n-1):
    s.add(end_arr[order[k]] == start_arr[order[k+1]])

# Flight connections
for k in range(n-1):
    i, j = order[k], order[k+1]
    s.add(Or([And(i == a, j == b) for a, b in allowed_pairs] + 
             [And(i == b, j == a) for a, b in allowed_pairs]))

# Solve and output
if s.check() == sat:
    model = s.model()
    # Extract order
    order_vals = [model.evaluate(o).as_long() for o in order]
    # Build day itinerary
    itinerary = []
    for day in range(1, 25):
        active = []
        for i in range(n):
            start_day = model.evaluate(start_vars[i]).as_long()
            end_day = model.evaluate(end_vars[i]).as_long()
            if start_day <= day <= end_day:
                active.append(index_to_city[i])
        place = active[0] if len(active) == 1 else sorted(active)
        itinerary.append({"day": day, "place": place})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")