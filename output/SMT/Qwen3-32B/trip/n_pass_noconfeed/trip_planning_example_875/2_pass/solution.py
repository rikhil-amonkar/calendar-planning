from z3 import *
import json  # Moved import to top of file

# Define cities and their durations
cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
num_cities = len(cities)
durations = [3, 4, 4, 2, 4, 5, 4]  # Stuttgart, Edinburgh, Athens, Split, Krakow, Venice, Mykonos

# Define allowed direct flights as pairs of city indices
direct_flights = [
    ('Krakow', 'Split'),
    ('Split', 'Athens'),
    ('Edinburgh', 'Krakow'),
    ('Venice', 'Stuttgart'),
    ('Krakow', 'Stuttgart'),
    ('Edinburgh', 'Stuttgart'),
    ('Stuttgart', 'Athens'),
    ('Venice', 'Edinburgh'),
    ('Athens', 'Mykonos'),
    ('Venice', 'Athens'),
    ('Stuttgart', 'Split'),
    ('Edinburgh', 'Athens'),
]

allowed_flights = set()
for a, b in direct_flights:
    a_idx = cities.index(a)
    b_idx = cities.index(b)
    allowed_flights.add((a_idx, b_idx))
    allowed_flights.add((b_idx, a_idx))

# Create Z3 solver
solver = Solver()

# Create before_ab variables (0 or 1)
before = [[Int(f'before_{a}_{b}') for b in range(num_cities)] for a in range(num_cities)]

# Constraints for before_ab
for a in range(num_cities):
    for b in range(num_cities):
        if a == b:
            solver.add(before[a][b] == 0)
        else:
            solver.add(before[a][b] + before[b][a] == 1)
            solver.add(Or(before[a][b] == 0, before[a][b] == 1))

# Transitivity constraints
for a in range(num_cities):
    for b in range(num_cities):
        for c in range(num_cities):
            if a != b or b != c or a != c:
                solver.add(before[a][b] + before[b][c] >= before[a][c])

# pos, days_before, start_day, end_day for each city
pos = [Int(f'pos_{c}') for c in range(num_cities)]
days_before = [Int(f'days_before_{c}') for c in range(num_cities)]
start_day = [Int(f'start_day_{c}') for c in range(num_cities)]
end_day = [Int(f'end_day_{c}') for c in range(num_cities)]

for c in range(num_cities):
    # pos[c] = sum_{a} before[a][c]
    solver.add(pos[c] == Sum([before[a][c] for a in range(num_cities)]))
    # days_before[c] = sum_{a} before[a][c] * durations[a]
    solver.add(days_before[c] == Sum([before[a][c] * durations[a] for a in range(num_cities)]))
    # start_day[c] = 1 + days_before[c] - pos[c]
    solver.add(start_day[c] == 1 + days_before[c] - pos[c])
    # end_day[c] = start_day[c] + durations[c] - 1
    solver.add(end_day[c] == start_day[c] + durations[c] - 1)

# Constraints for consecutive flights
for a in range(num_cities):
    for b in range(num_cities):
        if a != b:
            for c in range(num_cities):
                solver.add(Implies(before[a][b] == 1, Or(before[a][c] == 0, before[c][b] == 0)))
            if (a, b) not in allowed_flights:
                solver.add(before[a][b] == 0)

# Timing constraints
# Stuttgart (0): [start, end] overlaps with [11, 13]
solver.add(And(start_day[0] <= 13, end_day[0] >= 11))
# Split (3): [start, end] overlaps with [13, 14]
solver.add(And(start_day[3] <= 14, end_day[3] >= 13))
# Krakow (4): [start, end] overlaps with [8, 11]
solver.add(And(start_day[4] <= 11, end_day[4] >= 8))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract the order based on pos
    order_list = []
    for c in range(num_cities):
        p = model.evaluate(pos[c]).as_long()
        order_list.append((p, cities[c]))
    
    # Sort by position to get the order
    order_list.sort(key=lambda x: x[0])
    ordered_cities = [city for (p, city) in order_list]
    
    # Build the itinerary
    itinerary = []
    for city in ordered_cities:
        c_idx = cities.index(city)
        s = model.evaluate(start_day[c_idx]).as_long()
        e = model.evaluate(end_day[c_idx]).as_long()
        day_range = f"Day {s}-{e}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))