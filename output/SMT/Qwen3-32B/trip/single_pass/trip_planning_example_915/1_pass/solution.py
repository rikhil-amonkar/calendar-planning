from z3 import *
import json

# Define cities, durations, events, and allowed flights
cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
durations = {
    'Bucharest': 3,
    'Venice': 5,
    'Prague': 4,
    'Frankfurt': 5,
    'Zurich': 5,
    'Florence': 5,
    'Tallinn': 5
}
events = {
    'Venice': (22, 26),
    'Frankfurt': (12, 16),
    'Tallinn': (8, 12)
}

direct_flights = [
    ('Prague', 'Tallinn'),
    ('Prague', 'Zurich'),
    ('Florence', 'Prague'),
    ('Frankfurt', 'Bucharest'),
    ('Frankfurt', 'Venice'),
    ('Prague', 'Bucharest'),
    ('Bucharest', 'Zurich'),
    ('Tallinn', 'Frankfurt'),
    ('Zurich', 'Florence'),
    ('Frankfurt', 'Zurich'),
    ('Zurich', 'Venice'),
    ('Florence', 'Frankfurt'),
    ('Prague', 'Frankfurt'),
    ('Tallinn', 'Zurich'),
]

allowed_flights = set()
for a, b in direct_flights:
    allowed_flights.add((a, b))
    allowed_flights.add((b, a))

solver = Solver()

# Step 1: Position variables for each city
pos = {city: Int(f'pos_{city}') for city in cities}
for city in cities:
    solver.add(And(0 <= pos[city], pos[city] <= 6))
solver.add(Distinct([pos[city] for city in cities]))

# Step 2: Duration at each position
duration_at = [Int(f'duration_at_{i}') for i in range(7)]
for city in cities:
    for i in range(7):
        solver.add(Implies(pos[city] == i, duration_at[i] == durations[city]))

# Step 3: Start day at each position
start_day_at = [Int(f'start_day_at_{i}') for i in range(7)]
solver.add(start_day_at[0] == 1)
for i in range(1, 7):
    solver.add(start_day_at[i] == start_day_at[i-1] + duration_at[i-1] - 1)

# Step 4: Flight constraints
for a in cities:
    for b in cities:
        if a != b and (a, b) not in allowed_flights:
            solver.add(pos[a] + 1 != pos[b])

# Step 5: Event constraints
start_day = {}
for city in cities:
    start_day_var = Int(f'start_day_{city}')
    start_day[city] = start_day_var
    for i in range(7):
        solver.add(Implies(pos[city] == i, start_day_var == start_day_at[i]))

# Venice event constraint
solver.add(And(start_day['Venice'] <= 26, start_day['Venice'] + durations['Venice'] - 1 >= 22))
# Frankfurt event constraint
solver.add(And(start_day['Frankfurt'] <= 16, start_day['Frankfurt'] + durations['Frankfurt'] - 1 >= 12))
# Tallinn event constraint
solver.add(And(start_day['Tallinn'] <= 12, start_day['Tallinn'] + durations['Tallinn'] - 1 >= 8))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    # Generate the order of cities based on positions
    order = sorted(cities, key=lambda c: model.evaluate(pos[c]).as_long())
    # Generate itinerary
    day_to_city = {}
    for city in order:
        city_pos = model.evaluate(pos[city]).as_long()
        start = model.evaluate(start_day_at[city_pos]).as_long()
        end = start + durations[city] - 1
        for day in range(start, end + 1):
            day_to_city[day] = city
    # Create ordered itinerary list
    itinerary = [{day: day_to_city[day]} for day in range(1, 27)]
    print(json.dumps({'itinerary': itinerary}))
else:
    print("No solution found.")