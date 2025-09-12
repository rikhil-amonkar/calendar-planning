import z3
import json

solver = z3.Solver()

# Define cities and their indices
cities = ['Lyon', 'Paris', 'Riga', 'Berlin', 'Stockholm', 'Zurich', 'Nice', 'Seville', 'Milan', 'Naples']
city_indices = {city: idx for idx, city in enumerate(cities)}
durations = [3, 5, 2, 2, 3, 5, 2, 3, 3, 4]  # durations for each city index

# Parse allowed flights
allowed_flights = set()
flights_input = [
    ('Paris', 'Stockholm'),
    ('Seville', 'Paris'),
    ('Naples', 'Zurich'),
    ('Nice', 'Riga'),
    ('Berlin', 'Milan'),
    ('Paris', 'Zurich'),
    ('Paris', 'Nice'),
    ('Milan', 'Paris'),
    ('Milan', 'Riga'),
    ('Paris', 'Lyon'),
    ('Milan', 'Naples'),
    ('Paris', 'Riga'),
    ('Berlin', 'Stockholm'),
    ('Stockholm', 'Riga'),
    ('Nice', 'Zurich'),
    ('Milan', 'Zurich'),
    ('Lyon', 'Nice'),
    ('Zurich', 'Stockholm'),
    ('Zurich', 'Riga'),
    ('Berlin', 'Naples'),
    ('Milan', 'Stockholm'),
    ('Berlin', 'Zurich'),
    ('Milan', 'Seville'),
    ('Paris', 'Naples'),
    ('Berlin', 'Riga'),
    ('Nice', 'Stockholm'),
    ('Berlin', 'Paris'),
    ('Nice', 'Naples'),
    ('Berlin', 'Nice'),
]
for a, b in flights_input:
    a_idx = city_indices[a]
    b_idx = city_indices[b]
    allowed_flights.add((a_idx, b_idx))
    allowed_flights.add((b_idx, a_idx))

# Create order variables: order[0] to order[9]
order = [z3.Int(f'order_{i}') for i in range(10)]

# Constraints: each order[i] is between 0 and 9, and all distinct
for i in range(10):
    solver.add(z3.And(order[i] >= 0, order[i] <= 9))
solver.add(z3.Distinct(order))

# First city is Berlin (index 3)
solver.add(order[0] == 3)

# Create pos variables for each city
pos = [z3.Int(f'pos_{i}') for i in range(10)]

# Constraints: pos[c] is the position of city c in the order
for c in range(10):
    for i in range(10):
        solver.add(z3.Implies(order[i] == c, pos[c] == i))

# Constraints for consecutive flights
for i in range(9):
    # (order[i], order[i+1]) must be in allowed_flights
    # Create a condition that this pair is allowed
    allowed = False
    for a, b in allowed_flights:
        allowed = allowed | z3.And(order[i] == a, order[i+1] == b)
    solver.add(allowed)

# Constraints for sum_prev for Nice and Stockholm
# Nice: index 6
sum_prev_nice = 0
for d in range(10):
    if d != 6:
        sum_prev_nice += durations[d] * z3.If(pos[d] < pos[6], 1, 0)
solver.add(z3.Or(sum_prev_nice == 10, sum_prev_nice == 11))

# Stockholm: index 4
sum_prev_stockholm = 0
for d in range(10):
    if d != 4:
        sum_prev_stockholm += durations[d] * z3.If(pos[d] < pos[4], 1, 0)
solver.add(sum_prev_stockholm == 19)

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the order
    order_values = [model.evaluate(order[i]).as_long() for i in range(10)]
    # Map order_values to city names
    itinerary_order = [cities[order_values[i]] for i in range(10)]
    # Compute start days for each city in the order
    start_days = []
    current_day = 1
    for city_idx in order_values:
        start_days.append(current_day)
        current_day += durations[city_idx]
    # Create the day ranges
    result = []
    for i in range(10):
        city = itinerary_order[i]
        start_day = start_days[i]
        end_day = start_day + durations[city_indices[city]] - 1
        day_range = f"Day {start_day}-{end_day}"
        result.append({"day_range": day_range, "place": city})
    print(json.dumps({"itinerary": result}))
else:
    print("No solution found.")