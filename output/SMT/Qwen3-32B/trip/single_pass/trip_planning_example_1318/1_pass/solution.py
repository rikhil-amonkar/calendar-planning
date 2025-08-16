import z3
import json

# Define cities and their durations
cities = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
city_to_index = {city: idx for idx, city in enumerate(cities)}
durations = [2, 2, 3, 2, 5, 5, 5, 5, 4]  # Corresponds to each city in order

# Build allowed_flights set
allowed_flights = set()

bidirectional = [
    ("Porto", "Oslo"),
    ("Edinburgh", "Budapest"),
    ("Edinburgh", "Geneva"),
    ("Edinburgh", "Porto"),
    ("Vilnius", "Helsinki"),
    ("Riga", "Oslo"),
    ("Geneva", "Oslo"),
    ("Edinburgh", "Oslo"),
    ("Edinburgh", "Helsinki"),
    ("Vilnius", "Oslo"),
    ("Riga", "Helsinki"),
    ("Budapest", "Geneva"),
    ("Helsinki", "Budapest"),
    ("Helsinki", "Oslo"),
    ("Edinburgh", "Riga"),
    ("Tallinn", "Helsinki"),
    ("Geneva", "Porto"),
    ("Budapest", "Oslo"),
    ("Helsinki", "Geneva"),
    ("Tallinn", "Oslo"),
]

unidirectional = [
    ("Riga", "Tallinn"),
    ("Tallinn", "Vilnius"),
    ("Riga", "Vilnius"),
]

for a, b in bidirectional:
    allowed_flights.add((city_to_index[a], city_to_index[b]))
    allowed_flights.add((city_to_index[b], city_to_index[a]))

for a, b in unidirectional:
    allowed_flights.add((city_to_index[a], city_to_index[b]))

# Create Z3 solver
solver = z3.Solver()

# Create variables for the sequence of cities (positions 0 to 8)
pos = [z3.Int(f'pos_{i}') for i in range(9)]

# All cities must be distinct
solver.add(z3.Distinct(pos))

# Each city must be in 0-8
for p in pos:
    solver.add(z3.And(p >= 0, p <= 8))

# Consecutive cities must have allowed flights
for i in range(8):
    current = pos[i]
    next_city = pos[i+1]
    constraints = [z3.And(current == a, next_city == b) for a, b in allowed_flights]
    solver.add(z3.Or(constraints))

# Compute cum_dur and start_day for each position
cum_dur = [z3.Int(f'cum_dur_{i}') for i in range(10)]
solver.add(cum_dur[0] == 0)

for i in range(1, 10):
    solver.add(cum_dur[i] == cum_dur[i-1] + durations[pos[i-1]])

start_day = [z3.Int(f'start_day_{j}') for j in range(9)]
for j in range(9):
    solver.add(start_day[j] == cum_dur[j] - j + 1)

# Apply constraints for Oslo and Tallinn
for j in range(9):
    solver.add(z3.Implies(pos[j] == 0, z3.Or(start_day[j] == 23, start_day[j] == 24)))
    solver.add(z3.Implies(pos[j] == 4, start_day[j] <= 8))

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    sequence = [model.evaluate(p).as_long() for p in pos]
    days = [None] * 25

    for j in range(9):
        city_idx = sequence[j]
        city = cities[city_idx]
        days_in_city = durations[city_idx]
        start_day_j = model.evaluate(start_day[j]).as_long()
        end_day_j = start_day_j + days_in_city - 1
        for day_num in range(start_day_j, end_day_j + 1):
            days[day_num - 1] = city

    itinerary = [{'day': day + 1, 'city': city} for day, city in enumerate(days)]
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")