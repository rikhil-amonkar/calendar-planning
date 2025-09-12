from z3 import *
import json

# Define cities and their durations
cities = ['Manchester', 'Istanbul', 'Venice', 'Krakow', 'Lyon']
city_code = {city: i for i, city in enumerate(cities)}
durations = {
    'Manchester': 3,
    'Istanbul': 7,
    'Venice': 7,
    'Krakow': 6,
    'Lyon': 2
}

# Define allowed direct flights (both directions)
allowed_pairs = [
    ('Manchester', 'Venice'),
    ('Manchester', 'Istanbul'),
    ('Venice', 'Istanbul'),
    ('Istanbul', 'Krakow'),
    ('Venice', 'Lyon'),
    ('Lyon', 'Istanbul'),
    ('Manchester', 'Krakow'),
]

allowed_flights = set()
for a, b in allowed_pairs:
    allowed_flights.add((city_code[a], city_code[b]))
    allowed_flights.add((city_code[b], city_code[a]))

# Create Z3 variables for order, start, and end days
order = [Int(f'order_{i}') for i in range(5)]
start_days = [Int(f'start_{i}') for i in range(5)]
end_days = [Int(f'end_{i}') for i in range(5)]

solver = Solver()

# Constraints for order being a permutation of cities
for i in range(5):
    solver.add(And(order[i] >= 0, order[i] <= 4))
solver.add(Distinct(order))

# Constraints for transitions between consecutive cities
for i in range(4):
    prev = order[i]
    next_c = order[i + 1]
    constraints = [And(prev == a, next_c == b) for a, b in allowed_flights]
    solver.add(Or(constraints))

# First city starts on day 1
solver.add(start_days[0] == 1)

# Last city ends on day 21
solver.add(end_days[4] == 21)

# Constraints for end_days[i] = start_days[i] + duration - 1
for i in range(5):
    duration_expr = If(order[i] == 0, 3,
                       If(order[i] == 1, 7,
                          If(order[i] == 2, 7,
                             If(order[i] == 3, 6, 2))))
    solver.add(end_days[i] == start_days[i] + duration_expr - 1)

# Consecutive cities' end and start days
for i in range(4):
    solver.add(end_days[i] == start_days[i + 1])

# Constraints for Manchester's start day <= 3
for i in range(5):
    solver.add(Implies(order[i] == 0, start_days[i] <= 3))

# Constraints for Venice's start day <= 9
for i in range(5):
    solver.add(Implies(order[i] == 2, start_days[i] <= 9))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    order_values = [model.evaluate(order[i]).as_long() for i in range(5)]
    start_values = [model.evaluate(start_days[i]).as_long() for i in range(5)]
    end_values = [model.evaluate(end_days[i]).as_long() for i in range(5)]

    # Construct itinerary
    itinerary = []
    for i in range(5):
        city_name = cities[order_values[i]]
        start = start_values[i]
        end = end_values[i]
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})

    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")