from z3 import *
import json

# Define cities as integers
K, F, O, D, N = 0, 1, 2, 3, 4

# Durations
durations = {K: 5, F: 4, O: 3, D: 5, N: 5}

# Allowed connections
allowed_connections = {
    (K, F), (F, K),
    (F, O), (O, F),
    (D, F), (F, D),
    (K, O), (O, K),
    (D, O), (O, D),
    (N, O), (O, N),
    (N, D), (D, N),
    (N, F), (F, N),
}

# Create solver
s = Solver()

# Variables for the order of cities
order = [Int(f'order_{i}') for i in range(5)]

# Constraints: each city is between 0-4 and distinct
s.add(Distinct(order))
for city in order:
    s.add(And(0 <= city, city <= 4))

# Define start_days array
start_days = [Int(f'start_day_{i}') for i in range(5)]
s.add(start_days[0] == 1)

for i in range(1, 5):
    prev_city = order[i-1]
    duration_expr = If(prev_city == K, 5,
        If(prev_city == F, 4,
            If(prev_city == O, 3,
                If(prev_city == D, 5, 5)  # N is 5
            )
        )
    )
    s.add(start_days[i] == start_days[i-1] + duration_expr - 1)

# Now, determine start_O and start_D
start_O = Int('start_O')
s.add(Or(
    And(order[0] == O, start_O == start_days[0]),
    And(order[1] == O, start_O == start_days[1]),
    And(order[2] == O, start_O == start_days[2]),
    And(order[3] == O, start_O == start_days[3]),
    And(order[4] == O, start_O == start_days[4]),
))

start_D = Int('start_D')
s.add(Or(
    And(order[0] == D, start_D == start_days[0]),
    And(order[1] == D, start_D == start_days[1]),
    And(order[2] == D, start_D == start_days[2]),
    And(order[3] == D, start_D == start_days[3]),
    And(order[4] == D, start_D == start_days[4]),
))

# Constraints for Oslo and Dubrovnik
s.add(start_O == 16)
s.add(start_D <= 9)

# Add constraints for consecutive cities to have direct flights
for i in range(4):
    current = order[i]
    next_city = order[i+1]
    allowed = []
    for a, b in allowed_connections:
        allowed.append(And(current == a, next_city == b))
    s.add(Or(*allowed))

# Now, check if the solver can find a solution
if s.check() == sat:
    m = s.model()
    # Extract the order
    order_values = [m.eval(order[i]).as_long() for i in range(5)]
    # Extract start_days
    start_days_values = [m.eval(start_days[i]).as_long() for i in range(5)]
    # Now, generate the itinerary
    itinerary = []
    for i in range(5):
        city = order_values[i]
        start = start_days_values[i]
        duration = durations[city]
        end = start + duration - 1
        # For each day from start to end, add the city
        for day in range(start, end + 1):
            itinerary.append({day: city})
    # Map the city integers back to names
    city_names = {0: 'Krakow', 1: 'Frankfurt', 2: 'Oslo', 3: 'Dubrovnik', 4: 'Naples'}
    # Generate the list
    result = []
    for day_city in itinerary:
        day = list(day_city.keys())[0]
        city = day_city[day]
        result.append({'day': day, 'city': city_names[city]})
    # Sort by day
    result.sort(key=lambda x: x['day'])
    # Now, format as JSON with 'itinerary' key
    print(json.dumps({'itinerary': result}, indent=2))
else:
    print("No solution found.")