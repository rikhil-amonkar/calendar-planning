from z3 import *
import json

# Define cities and their durations
cities = {
    'Oslo': 0,
    'Reykjavik': 1,
    'Stockholm': 2,
    'Munich': 3,
    'Frankfurt': 4,
    'Barcelona': 5,
    'Bucharest': 6,
    'Split': 7
}

durations = [2, 5, 4, 4, 4, 3, 2, 3]  # Corresponds to cities 0-7

# Direct flights
direct_flights = [
    ('Reykjavik', 'Munich'),
    ('Munich', 'Frankfurt'),
    ('Split', 'Oslo'),
    ('Reykjavik', 'Oslo'),
    ('Bucharest', 'Munich'),
    ('Oslo', 'Frankfurt'),
    ('Bucharest', 'Barcelona'),
    ('Barcelona', 'Frankfurt'),
    ('Reykjavik', 'Frankfurt'),
    ('Barcelona', 'Stockholm'),
    ('Barcelona', 'Reykjavik'),
    ('Stockholm', 'Reykjavik'),
    ('Barcelona', 'Split'),
    ('Bucharest', 'Oslo'),
    ('Bucharest', 'Frankfurt'),
    ('Split', 'Stockholm'),
    ('Barcelona', 'Oslo'),
    ('Stockholm', 'Munich'),
    ('Stockholm', 'Oslo'),
    ('Split', 'Frankfurt'),
    ('Barcelona', 'Munich'),
    ('Stockholm', 'Frankfurt'),
    ('Munich', 'Oslo'),
    ('Split', 'Munich'),
]

allowed_transitions = set()
for a, b in direct_flights:
    c1 = cities[a]
    c2 = cities[b]
    allowed_transitions.add((c1, c2))
    allowed_transitions.add((c2, c1))

# Z3 solver
solver = Solver()

# Define sequence of cities (permutation of 0-7)
seq = [Int(f'seq_{i}') for i in range(8)]
solver.add(Distinct(seq))
for i in range(8):
    solver.add(And(seq[i] >= 0, seq[i] <= 7))

# Define start days for each city in the sequence
start_days = [Int(f'start_{i}') for i in range(8)]
solver.add(start_days[0] == 1)
for i in range(1, 8):
    prev_city = seq[i-1]
    prev_duration = durations[prev_city]
    solver.add(start_days[i] == start_days[i-1] + prev_duration - 1)

# Add constraints for specific cities
for i in range(8):
    # Oslo (0)
    solver.add(Implies(seq[i] == 0, start_days[i] == 16))
    solver.add(Implies(seq[i] == 0, start_days[i] + durations[0] - 1 == 17))
    # Reykjavik (1)
    solver.add(Implies(seq[i] == 1, And(start_days[i] <= 13, start_days[i] >= 5)))
    # Munich (3)
    solver.add(Implies(seq[i] == 3, And(start_days[i] <= 16, start_days[i] >= 10)))
    # Frankfurt (4)
    solver.add(Implies(seq[i] == 4, And(start_days[i] <= 20, start_days[i] >= 14)))

# Add transition constraints between consecutive cities
for i in range(7):
    a = seq[i]
    b = seq[i+1]
    transitions_expr = Or([And(a == x, b == y) for x, y in allowed_transitions])
    solver.add(transitions_expr)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Extract the sequence and start_days
    seq_vals = [model.evaluate(seq[i]).as_long() for i in range(8)]
    start_vals = [model.evaluate(start_days[i]).as_long() for i in range(8)]
    
    # Build the itinerary
    itinerary = []
    for i in range(8):
        city_id = seq_vals[i]
        start = start_vals[i]
        end = start + durations[city_id] - 1
        city_name = [k for k, v in cities.items() if v == city_id][0]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city_name
        })
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")