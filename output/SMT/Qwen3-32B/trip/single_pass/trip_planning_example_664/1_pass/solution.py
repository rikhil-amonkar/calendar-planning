from z3 import *
import json

# City and duration mapping
cities = {
    'Tallinn': 0,
    'Bucharest': 1,
    'Seville': 2,
    'Stockholm': 3,
    'Munich': 4,
    'Milan': 5
}

durations = {
    0: 2,
    1: 4,
    2: 5,
    3: 5,
    4: 5,
    5: 2
}

direct_flights = {
    (0, 3), (3, 0),  # Stockholm and Tallinn
    (1, 4), (4, 1),  # Bucharest and Munich
    (4, 2), (2, 4),  # Munich and Seville
    (4, 3), (3, 4),  # Munich and Stockholm
    (4, 5), (5, 4),  # Munich and Milan
    (5, 3), (3, 5),  # Milan and Stockholm
    (5, 2), (2, 5)   # Seville and Milan
}

# Z3 solver setup
s = Solver()

order = [Int(f'order_{i}') for i in range(6)]

# All cities are in 0-5 and distinct
s.add(Distinct(order))
for i in range(6):
    s.add(And(order[i] >= 0, order[i] <= 5))

# Fixed positions
s.add(order[0] == 1)  # Bucharest
s.add(order[1] == 4)  # Munich
s.add(order[2] == 2)  # Seville

# Remaining cities: 0 (Tallinn), 3 (Stockholm), 5 (Milan)
s.add(Or([order[3] == 0, order[3] == 3, order[3] == 5]))
s.add(Or([order[4] == 0, order[4] == 3, order[4] == 5]))
s.add(Or([order[5] == 0, order[5] == 3, order[5] == 5]))
s.add(Distinct(order[3], order[4], order[5]))

# Flight constraints
for i in range(5):
    a, b = order[i], order[i + 1]
    allowed = [And(a == x, b == y) for x, y in direct_flights]
    s.add(Or(allowed))

# Solve and generate itinerary
if s.check() == sat:
    model = s.model()
    order_values = [model[order[i]].as_long() for i in range(6)]
    city_names = {v: k for k, v in cities.items()}

    # Compute start and end days
    start_days = [1]
    for i in range(1, 6):
        prev_city = order_values[i - 1]
        start_days.append(start_days[i - 1] + durations[prev_city] - 1)

    # Generate itinerary
    itinerary = []
    for i in range(6):
        city_id = order_values[i]
        city_name = city_names[city_id]
        start = start_days[i]
        end = start_days[i] + durations[city_id] - 1
        for day in range(start, end + 1):
            itinerary.append({"day": day, "city": city_name})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")