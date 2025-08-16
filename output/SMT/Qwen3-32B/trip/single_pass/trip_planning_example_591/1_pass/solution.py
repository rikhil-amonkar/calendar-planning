import z3
import json

# Define cities and their codes
city_names = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
city_codes = {name: i for i, name in enumerate(city_names)}
durations = {
    'Stuttgart': 2,
    'Bucharest': 2,
    'Geneva': 4,
    'Valencia': 6,
    'Munich': 7
}

# Define allowed flights
allowed_pairs = [
    ('Geneva', 'Munich'),
    ('Munich', 'Valencia'),
    ('Bucharest', 'Valencia'),
    ('Munich', 'Bucharest'),
    ('Valencia', 'Stuttgart'),
    ('Geneva', 'Valencia'),
]
allowed_flights_set = set()
for a, b in allowed_pairs:
    allowed_flights_set.add((city_codes[a], city_codes[b]))
    allowed_flights_set.add((city_codes[b], city_codes[a]))

# Z3 solver setup
solver = z3.Solver()

# Variables for the sequence of cities
seq = [z3.Int(f'seq_{i}') for i in range(5)]
# Variables for the start day of each position in the sequence
s_day = [z3.Int(f's_day_{i}') for i in range(5)]

# Constraints for sequence to be a permutation of 0-4
solver.add(z3.And([z3.And(0 <= seq[i], seq[i] <= 4) for i in range(5)]))
solver.add(z3.Distinct(seq))

# First start day is 1
solver.add(s_day[0] == 1)

# Calculate start days based on previous city's duration
for i in range(1, 5):
    prev_code = seq[i-1]
    # Determine duration of previous city
    duration_prev = z3.If(prev_code == 0, 2,
                          z3.If(prev_code == 1, 2,
                          z3.If(prev_code == 2, 4,
                          z3.If(prev_code == 3, 6, 7))))
    solver.add(s_day[i] == s_day[i-1] + duration_prev - 1)

# Ensure consecutive cities have allowed flights
for i in range(4):
    current = seq[i]
    next_city = seq[i+1]
    constraints = []
    for a, b in allowed_flights_set:
        constraints.append(z3.And(current == a, next_city == b))
    solver.add(z3.Or(constraints))

# Constraints for Geneva and Munich
for i in range(5):
    # Geneva (code 2) must start on or before day 4
    solver.add(z3.Implies(seq[i] == 2, s_day[i] <= 4))
    # Munich (code 4) must start on or before day 10
    solver.add(z3.Implies(seq[i] == 4, s_day[i] <= 10))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    # Extract sequence and start days
    sequence = [model.evaluate(seq[i]).as_long() for i in range(5)]
    start_days = [model.evaluate(s_day[i]).as_long() for i in range(5)]
    
    # Build itinerary
    itinerary = {}
    for i in range(5):
        city_code = sequence[i]
        city_name = city_names[city_code]
        start = start_days[i]
        duration = durations[city_name]
        end = start + duration - 1
        for day in range(start, end + 1):
            itinerary[day] = city_name
    
    # Sort days and format JSON
    sorted_days = sorted(itinerary.keys())
    result = {
        'itinerary': [{'day': day, 'city': itinerary[day]} for day in sorted_days]
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")