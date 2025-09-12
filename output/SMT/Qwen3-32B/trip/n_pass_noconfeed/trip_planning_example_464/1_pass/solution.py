from z3 import *
import json

# Define cities and their indices
cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
city_indices = {city: idx for idx, city in enumerate(cities)}
durations_list = [5, 4, 3, 5, 5]  # Durations for each city in the same order as cities

# Define direct flights between cities (bidirectional)
direct_flights = [
    ('Dubrovnik', 'Oslo'),
    ('Frankfurt', 'Krakow'),
    ('Frankfurt', 'Oslo'),
    ('Dubrovnik', 'Frankfurt'),
    ('Krakow', 'Oslo'),
    ('Naples', 'Oslo'),
    ('Naples', 'Dubrovnik'),
    ('Naples', 'Frankfurt'),
]

# Convert direct flights to city index pairs (both directions)
direct_flights_set = set()
for a, b in direct_flights:
    a_idx = city_indices[a]
    b_idx = city_indices[b]
    direct_flights_set.add((a_idx, b_idx))
    direct_flights_set.add((b_idx, a_idx))

# Initialize Z3 solver
solver = Solver()

# Variables: order[i] is the index of the i-th city in the itinerary
order = [Int(f'order_{i}') for i in range(5)]
# Variables: start_days[i] is the start day of the i-th city
start_days = [Int(f'start_day_{i}') for i in range(5)]

# Constraints: order is a permutation of 0-4
solver.add(And([0 <= order[i], order[i] <= 4 for i in range(5)]))
solver.add(Distinct(order))

# Constraints: calculate start_days based on previous durations
solver.add(start_days[0] == 1)
for i in range(1, 5):
    solver.add(start_days[i] == start_days[i-1] + durations_list[order[i-1]])

# Constraints: Dubrovnik's start day must be 5
for i in range(5):
    solver.add(If(order[i] == 3, start_days[i] == 5, True == True))

# Constraints: Oslo's start day must be 16
for i in range(5):
    solver.add(If(order[i] == 2, start_days[i] == 16, True == True))

# Constraints: transitions between consecutive cities must be direct flights
for i in range(4):
    transitions = []
    for a, b in direct_flights_set:
        transitions.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(transitions))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract the order and start_days
    order_vals = [model.eval(order[i]).as_long() for i in range(5)]
    start_day_vals = [model.eval(start_days[i]).as_long() for i in range(5)]
    
    # Build the itinerary
    itinerary = []
    for i in range(5):
        city = cities[order_vals[i]]
        duration = durations_list[order_vals[i]]
        start_day = start_day_vals[i]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output the result as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"error": "No solution found"}, indent=2))