import z3
import json

# Define cities and their durations
city_durations = [
    (0, 4),  # Istanbul
    (1, 4),  # Vienna
    (2, 2),  # Riga
    (3, 2),  # Brussels
    (4, 4),  # Madrid
    (5, 4),  # Vilnius
    (6, 5),  # Venice
    (7, 4),  # Geneva
    (8, 5),  # Munich
    (9, 2),  # Reykjavik
]

# Event constraints: (city_id, required_start_day)
event_constraints = {
    3: 26,  # Brussels
    5: 20,  # Vilnius
    6: 7,   # Venice
    7: 1,   # Geneva
}

# Define allowed direct flights as pairs of city IDs
allowed_flights = set()
for a, b in [
    (8, 1), (1, 8), (0, 3), (3, 0), (1, 5), (5, 1), (4, 8), (8, 4),
    (6, 3), (3, 6), (2, 3), (3, 2), (7, 0), (0, 7), (8, 9), (9, 8),
    (1, 0), (0, 1), (2, 0), (0, 2), (9, 1), (1, 9), (6, 8), (8, 6),
    (4, 6), (6, 4), (5, 0), (0, 5), (6, 1), (1, 6), (6, 0), (0, 6),
    (9, 4), (4, 9), (2, 8), (8, 2), (8, 0), (0, 8), (9, 3), (3, 9),
    (5, 3), (3, 5), (5, 8), (8, 5), (4, 1), (1, 4), (1, 2), (2, 1),
    (7, 1), (1, 7), (4, 3), (3, 4), (1, 3), (3, 1), (7, 3), (3, 7),
    (7, 4), (4, 7), (8, 3), (3, 8), (4, 0), (0, 4), (7, 8), (8, 7),
    (2, 5), (5, 2)
]:
    allowed_flights.add((a, b))

# Create solver and variables
solver = z3.Solver()
order = [z3.Int(f'order_{i}') for i in range(10)]
start_day = [z3.Int(f'start_day_{i}') for i in range(10)]
end_day = [z3.Int(f'end_day_{i}') for i in range(10)]

# Add constraints for order to be a permutation of cities 0-9
solver.add(z3.Distinct(order))
for var in order:
    solver.add(var >= 0, var <= 9)

# Add constraints for start_day and end_day
solver.add(start_day[0] == 1)
for i in range(1, 10):
    solver.add(start_day[i] == end_day[i-1])

# Function to build duration expressions
def build_duration_expr(city_var):
    expr = 0
    for city_id, dur in city_durations:
        if expr == 0:
            expr = z3.If(city_var == city_id, dur, 0)
        else:
            expr = z3.If(city_var == city_id, dur, expr)
    return expr

# Add constraints for end_day based on durations
for i in range(10):
    duration_expr = build_duration_expr(order[i])
    solver.add(end_day[i] == start_day[i] + duration_expr - 1)

# Add constraints for allowed transitions between consecutive cities
for i in range(9):
    a, b = order[i], order[i+1]
    constraints = []
    for (x, y) in allowed_flights:
        constraints.append(z3.And(a == x, b == y))
    solver.add(z3.Or(constraints))

# Add constraints for event-specific cities
for city_id, required_start in event_constraints.items():
    for i in range(10):
        solver.add(z3.Implies(order[i] == city_id, start_day[i] == required_start))

# Check for solution and output result
if solver.check() == z3.sat:
    model = solver.model()
    order_values = [model.eval(order[i]).as_long() for i in range(10)]
    start_day_values = [model.eval(start_day[i]).as_long() for i in range(10)]
    end_day_values = [model.eval(end_day[i]).as_long() for i in range(10)]
    
    city_names = {
        0: 'Istanbul',
        1: 'Vienna',
        2: 'Riga',
        3: 'Brussels',
        4: 'Madrid',
        5: 'Vilnius',
        6: 'Venice',
        7: 'Geneva',
        8: 'Munich',
        9: 'Reykjavik',
    }
    
    itinerary = []
    for i in range(10):
        city_id = order_values[i]
        city_name = city_names[city_id]
        start = start_day_values[i]
        end = end_day_values[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))