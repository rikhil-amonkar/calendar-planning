import json
from z3 import *

cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul', 'Milan', 'Vilnius', 'Frankfurt']
num_cities = len(cities)
durations = {
    'Brussels': 3,
    'Helsinki': 3,
    'Split': 4,
    'Dubrovnik': 2,
    'Istanbul': 5,
    'Milan': 4,
    'Vilnius': 5,
    'Frankfurt': 3
}

direct_flights = [
    ('Milan', 'Frankfurt'),
    ('Split', 'Frankfurt'),
    ('Milan', 'Split'),
    ('Brussels', 'Vilnius'),
    ('Brussels', 'Helsinki'),
    ('Istanbul', 'Brussels'),
    ('Milan', 'Vilnius'),
    ('Brussels', 'Milan'),
    ('Istanbul', 'Helsinki'),
    ('Helsinki', 'Vilnius'),
    ('Helsinki', 'Dubrovnik'),
    ('Split', 'Vilnius'),
    ('Dubrovnik', 'Istanbul'),
    ('Istanbul', 'Milan'),
    ('Helsinki', 'Frankfurt'),
    ('Istanbul', 'Frankfurt'),
    ('Brussels', 'Frankfurt'),
    ('Dubrovnik', 'Frankfurt'),
    ('Frankfurt', 'Vilnius'),
]

# Convert direct_flights to bidirectional pairs
direct_flight_pairs = set()
for a, b in direct_flights:
    a_idx = cities.index(a)
    b_idx = cities.index(b)
    direct_flight_pairs.add((a_idx, b_idx))
    direct_flight_pairs.add((b_idx, a_idx))  # Assuming bidirectional flights

# Create Z3 solver
s = Solver()

# Define sequence variables (each is an integer representing city index)
sequence = [Int(f'seq_{i}') for i in range(num_cities)]

# Constraints: all elements are distinct and in range
for city_var in sequence:
    s.add(And(0 <= city_var, city_var < num_cities))
s.add(Distinct(sequence))

# Define start_days variables
start_days = [Int(f'start_{i}') for i in range(num_cities)]
s.add(start_days[0] == 1)

for i in range(1, num_cities):
    prev_city = sequence[i-1]
    prev_duration = durations[cities[prev_city]]
    s.add(start_days[i] == start_days[i-1] + prev_duration - 1)

# Direct flight constraints between consecutive cities
for i in range(num_cities - 1):
    current_city = sequence[i]
    next_city = sequence[i+1]
    allowed = Or([And(current_city == a, next_city == b) for (a, b) in direct_flight_pairs])
    s.add(allowed)

# Event constraints: Istanbul must start on day 1, Vilnius on day 18, Frankfurt on day 16
for i in range(num_cities):
    # Istanbul (index 4) must start on day 1
    s.add(Implies(sequence[i] == 4, start_days[i] == 1))
    # Vilnius (index 6) must start on day 18
    s.add(Implies(sequence[i] == 6, start_days[i] == 18))
    # Frankfurt (index 7) must start on day 16
    s.add(Implies(sequence[i] == 7, start_days[i] == 16))

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    
    # Extract the sequence and start_days
    seq = [model.eval(sequence[i]).as_long() for i in range(num_cities)]
    start_days_vals = [model.eval(start_days[i]).as_long() for i in range(num_cities)]
    
    # Build the itinerary
    itinerary = []
    for i in range(num_cities):
        city_idx = seq[i]
        city_name = cities[city_idx]
        start = start_days_vals[i]
        duration = durations[city_name]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))