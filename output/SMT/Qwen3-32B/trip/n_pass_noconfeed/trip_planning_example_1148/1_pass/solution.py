import json
from z3 import *

# Define cities and durations
cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
durations = {
    'Lisbon': 2,
    'Dubrovnik': 5,
    'Copenhagen': 5,
    'Prague': 3,
    'Tallinn': 2,
    'Stockholm': 4,
    'Split': 3,
    'Lyon': 2
}

# Define direct flights
direct_flights = [
    ('Dubrovnik', 'Stockholm'),
    ('Lisbon', 'Copenhagen'),
    ('Lisbon', 'Lyon'),
    ('Copenhagen', 'Stockholm'),
    ('Copenhagen', 'Split'),
    ('Prague', 'Stockholm'),
    ('Tallinn', 'Stockholm'),
    ('Prague', 'Lyon'),
    ('Lisbon', 'Stockholm'),
    ('Prague', 'Lisbon'),
    ('Stockholm', 'Split'),
    ('Prague', 'Copenhagen'),
    ('Split', 'Lyon'),
    ('Copenhagen', 'Dubrovnik'),
    ('Prague', 'Split'),
    ('Tallinn', 'Copenhagen'),
    ('Tallinn', 'Prague'),
]

# Generate allowed transitions (both directions)
allowed_transitions = set()
for a, b in direct_flights:
    allowed_transitions.add((a, b))
    allowed_transitions.add((b, a))

# Create Z3 solver
solver = Solver()

# Create position variables for each city
positions = {city: Int(f'pos_{city}') for city in cities}

# Add constraints: positions are between 0 and 7, and distinct
for city in cities:
    solver.add(And(positions[city] >= 0, positions[city] <= 7))
solver.add(Distinct([positions[city] for city in cities]))

# Compute start_days for each city
start_days = {}
for city in cities:
    sum_prev_durations = 0
    for other in cities:
        sum_prev_durations += If(positions[other] < positions[city], durations[other], 0)
    p = positions[city]
    start_days[city] = 1 + sum_prev_durations - p

# Add constraints on specific start days
solver.add(start_days['Lisbon'] == 4)
solver.add(start_days['Tallinn'] == 1)
solver.add(And(start_days['Stockholm'] >= 10, start_days['Stockholm'] <= 16))
solver.add(start_days['Lyon'] == 18)

# Add constraints for transitions
for A in cities:
    for B in cities:
        if A == B:
            continue
        if (A, B) not in allowed_transitions:
            solver.add(positions[B] != positions[A] + 1)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Extract positions and start days from the model
    city_pos = {city: model.eval(positions[city]).as_long() for city in cities}
    city_start_days = {city: model.eval(start_days[city]).as_long() for city in cities}
    
    # Sort cities by their position to get the order
    ordered_cities = sorted(cities, key=lambda c: city_pos[c])
    
    # Generate the itinerary
    itinerary = []
    for city in ordered_cities:
        start = city_start_days[city]
        duration = durations[city]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")