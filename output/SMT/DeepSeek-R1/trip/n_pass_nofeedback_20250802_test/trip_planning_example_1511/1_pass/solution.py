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

# Fixed start days: Munich (2) starts at 4, Santorini (3) at 8, Valencia (8) at 14
fixed_starts = {2: 4, 3: 8, 8: 14}

# Define the direct flight connections as tuples of city names
connections = [
    ("Bucharest", "Manchester"),
    ("Munich", "Venice"), ("Munich", "Venice"),  # Corrected to "Munich"
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

# Z3 setup
s = Solver()

# Arrays for start and end days of each city
start = [Int('start_%d' % i) for i in range(10)]
end = [Int('end_%d' % i) for i in range(10)]

# Order: list of 10 integers representing the sequence of cities
order = [Int('order_%d' % i) for i in range(10)]

# Each element in order must be between 0 and 9
for i in range(10):
    s.add(And(order[i] >= 0, order[i] < 10))
s.add(Distinct(order))

# Duration constraints
for i in range(10):
    s.add(end[i] == start[i] + durations[i] - 1)

# Fixed start days
s.add(start[2] == 4)
s.add(start[3] == 8)
s.add(start[8] == 14)

# Chain constraints: first city starts at day 1, last ends at day 24, consecutive cities have matching end and start
s.add(start[order[0]] == 1)
s.add(end[order[9]] == 24)
for j in range(9):
    s.add(end[order[j]] == start[order[j+1]])

# Flight connection constraints for consecutive cities in the order
for j in range(9):
    a = order[j]
    b = order[j+1]
    conds = []
    for (x, y) in allowed_pairs:
        conds.append(Or(And(a == x, b == y), And(a == y, b == x)))
    s.add(Or(conds))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    # Extract the order as a list of integers
    order_indices = [model.evaluate(order[i]).as_long() for i in range(10)]
    # Extract start and end days for each city
    start_days = [model.evaluate(start[i]).as_long() for i in range(10)]
    end_days = [model.evaluate(end[i]).as_long() for i in range(10)]
    
    # Build itinerary for each day
    itinerary = []
    for d in range(1, 25):  # Days 1 to 24
        active_cities = []  # List of (start_day, city_name) active on day d
        for i in range(10):
            s_day = start_days[i]
            e_day = end_days[i]
            if s_day <= d <= e_day:
                active_cities.append((s_day, index_to_city[i]))
        # Sort active cities by their start day
        active_cities_sorted = sorted(active_cities, key=lambda x: x[0])
        city_names = [item[1] for item in active_cities_sorted]
        # If one city, output as string; else as list
        if len(city_names) == 1:
            place = city_names[0]
        else:
            place = city_names
        itinerary.append({"day": d, "place": place})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")