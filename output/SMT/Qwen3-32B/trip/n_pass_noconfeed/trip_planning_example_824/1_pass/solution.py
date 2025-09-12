from z3 import *
import json

# Define cities and their indexes
cities = ['Berlin', 'Split', 'Bucharest', 'Riga', 'Lisbon', 'Tallinn', 'Lyon']
durations = [5, 3, 3, 5, 3, 4, 5]  # durations for each city in the order of cities list

# Define allowed direct flights as (from, to) tuples
allowed_edges = set()
allowed_edges.add((4, 2))  # Lisbon and Bucharest
allowed_edges.add((2, 4))
allowed_edges.add((0, 4))  # Berlin and Lisbon
allowed_edges.add((4, 0))
allowed_edges.add((2, 3))  # Bucharest and Riga
allowed_edges.add((3, 2))
allowed_edges.add((0, 3))  # Berlin and Riga
allowed_edges.add((3, 0))
allowed_edges.add((1, 6))  # Split and Lyon
allowed_edges.add((6, 1))
allowed_edges.add((4, 3))  # Lisbon and Riga
allowed_edges.add((3, 4))
allowed_edges.add((3, 5))  # Riga to Tallinn
allowed_edges.add((0, 1))  # Berlin and Split
allowed_edges.add((1, 0))
allowed_edges.add((6, 4))  # Lyon and Lisbon
allowed_edges.add((4, 6))
allowed_edges.add((0, 5))  # Berlin and Tallinn
allowed_edges.add((5, 0))
allowed_edges.add((6, 2))  # Lyon and Bucharest
allowed_edges.add((2, 6))

# Create Z3 solver
s = Solver()

# Define order variables: first city is Berlin (index 0)
order_vars = [0] + [Int(f'order_{i}') for i in range(1, 7)]

# Add constraints: all cities must be unique and in range 1-6 for positions 1-6
s.add(Distinct(order_vars))
for i in range(1, 7):
    s.add(And(1 <= order_vars[i], order_vars[i] <= 6))

# Add constraints for allowed transitions between consecutive cities
for i in range(6):
    prev = order_vars[i]
    next_c = order_vars[i + 1]
    transitions = []
    for (p, n) in allowed_edges:
        transitions.append(And(prev == p, next_c == n))
    s.add(Or(transitions))

# Define start days for each city in the order
start_days = [Int(f'start_{i}') for i in range(7)]
s.add(start_days[0] == 1)  # Berlin starts on day 1

for i in range(1, 7):
    # Compute duration of the previous city based on order_vars[i-1]
    duration_prev = If(order_vars[i - 1] == 0, 5,
                       If(order_vars[i - 1] == 1, 3,
                          If(order_vars[i - 1] == 2, 3,
                             If(order_vars[i - 1] == 3, 5,
                                If(order_vars[i - 1] == 4, 3,
                                   If(order_vars[i - 1] == 5, 4, 5))))))
    s.add(start_days[i] == start_days[i - 1] + duration_prev - 1)

# Add constraints for Lyon (index 6) and Bucharest (index 2)
for i in range(7):
    # Lyon: start_day must be between 3 and 11 inclusive
    s.add(Implies(order_vars[i] == 6, And(start_days[i] <= 11, start_days[i] >= 3)))
    # Bucharest: start_day must be between 11 and 15 inclusive
    s.add(Implies(order_vars[i] == 2, And(start_days[i] <= 15, start_days[i] >= 11)))

# Check for solution
if s.check() == sat:
    model = s.model()
    # Extract order and start days
    order = [model[order_vars[i]].as_long() for i in range(7)]
    starts = [model[start_days[i]].as_long() for i in range(7)]
    # Build itinerary
    itinerary = []
    for i in range(7):
        city_index = order[i]
        city_name = cities[city_index]
        start_day = starts[i]
        duration_city = durations[city_index]
        end_day = start_day + duration_city - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    # Output JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))