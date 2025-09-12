import z3
import json

# Define cities and their indices
cities = ['Santorini', 'Valencia', 'Madrid', 'Seville', 'Bucharest', 'Vienna', 'Riga', 'Tallinn', 'Krakow', 'Frankfurt']
city_indices = {city: i for i, city in enumerate(cities)}

# Durations for each city
durations = [3, 4, 2, 2, 3, 4, 4, 5, 5, 4]  # index 0-9

# Build allowed_transitions
allowed_transitions = set()
pairs = [
    ('Vienna', 'Bucharest'),
    ('Santorini', 'Madrid'),
    ('Seville', 'Valencia'),
    ('Vienna', 'Seville'),
    ('Madrid', 'Valencia'),
    ('Bucharest', 'Riga'),
    ('Valencia', 'Bucharest'),
    ('Santorini', 'Bucharest'),
    ('Vienna', 'Valencia'),
    ('Vienna', 'Madrid'),
    ('Valencia', 'Krakow'),
    ('Valencia', 'Frankfurt'),
    ('Krakow', 'Frankfurt'),
    ('Riga', 'Tallinn'),
    ('Vienna', 'Krakow'),
    ('Vienna', 'Frankfurt'),
    ('Madrid', 'Seville'),
    ('Santorini', 'Vienna'),
    ('Vienna', 'Riga'),
    ('Frankfurt', 'Tallinn'),
    ('Frankfurt', 'Bucharest'),
    ('Madrid', 'Bucharest'),
    ('Frankfurt', 'Riga'),
    ('Madrid', 'Frankfurt'),
]

for a, b in pairs:
    i = city_indices[a]
    j = city_indices[b]
    allowed_transitions.add((i, j))
    allowed_transitions.add((j, i))

# Create Z3 solver
s = z3.Solver()

# Create cities_order variables
cities_order = [z3.Int('city_{}'.format(i)) for i in range(10)]

# Add constraints that cities_order is a permutation of 0-9
s.add(z3.Distinct(cities_order))
for i in range(10):
    s.add(z3.And(cities_order[i] >= 0, cities_order[i] <= 9))

# Add allowed transitions between consecutive cities
for i in range(9):
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(z3.And(cities_order[i] == a, cities_order[i+1] == b))
    s.add(z3.Or(*constraints))

# Create start_days variables
start_days = [z3.Int('start_day_{}'.format(i)) for i in range(10)]

# Define durations_z3 function
durations_z3 = z3.Function('durations_z3', z3.IntSort(), z3.IntSort())
for i in range(10):
    s.add(durations_z3(i) == durations[i])

# Add start_days constraints
s.add(start_days[0] == 1)
for i in range(1, 10):
    s.add(start_days[i] == start_days[i-1] + durations_z3(cities_order[i-1]) - 1)

# Add event constraints
for i in range(10):
    # Madrid (index 2) must start on day 6
    s.add(z3.Implies(cities_order[i] == 2, start_days[i] == 6))
    # Riga (index 6) must start on day 20
    s.add(z3.Implies(cities_order[i] == 6, start_days[i] == 20))
    # Tallinn (index 7) must start on day 23
    s.add(z3.Implies(cities_order[i] == 7, start_days[i] == 23))
    # Vienna (index 5) must start on or before day 6
    s.add(z3.Implies(cities_order[i] == 5, start_days[i] <= 6))
    # Krakow (index 8) must start between 7 and 15 inclusive
    s.add(z3.Implies(cities_order[i] == 8, z3.And(start_days[i] >= 7, start_days[i] <= 15)))

# Check if the model is satisfiable
if s.check() == z3.sat:
    model = s.model()
    # Extract cities_order and start_days
    cities_order_values = [model.eval(cities_order[i]).as_long() for i in range(10)]
    start_days_values = [model.eval(start_days[i]).as_long() for i in range(10)]
    
    # Generate the itinerary
    itinerary = []
    for i in range(10):
        city_idx = cities_order_values[i]
        city_name = cities[city_idx]
        start_day = start_days_values[i]
        end_day = start_day + durations[city_idx] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")