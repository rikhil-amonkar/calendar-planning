import z3

solver = z3.Solver()

# City indices: Berlin=0, Nice=1, Athens=2, Stockholm=3, Barcelona=4, Vilnius=5, Lyon=6
durations = {0: 3, 1: 5, 2: 5, 3: 5, 4: 2, 5: 4, 6: 2}

allowed_transitions = [
    (6, 1), (1, 6),  # Lyon-Nice
    (3, 2), (2, 3),  # Stockholm-Athens
    (1, 2), (2, 1),  # Nice-Athens
    (0, 2), (2, 0),  # Berlin-Athens
    (0, 1), (1, 0),  # Berlin-Nice
    (0, 4), (4, 0),  # Berlin-Barcelona
    (0, 5), (5, 0),  # Berlin-Vilnius
    (4, 1), (1, 4),  # Barcelona-Nice
    (2, 5), (5, 2),  # Athens-Vilnius
    (0, 3), (3, 0),  # Berlin-Stockholm
    (1, 3), (3, 1),  # Nice-Stockholm
    (4, 2), (2, 4),  # Barcelona-Athens
    (4, 3), (3, 4),  # Barcelona-Stockholm
    (4, 6), (6, 4),  # Barcelona-Lyon
]

# Create variables for the cities in the sequence
cities = [z3.Int(f'c{i}') for i in range(7)]

# All cities are distinct
solver.add(z3.Distinct(cities))

# All cities are in 0-6
for c in cities:
    solver.add(z3.And(c >= 0, c <= 6))

# First city is Berlin (0)
solver.add(cities[0] == 0)

# Consecutive transitions must be allowed
for i in range(6):
    current = cities[i]
    next_c = cities[i+1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(z3.And(current == a, next_c == b))
    solver.add(z3.Or(constraints))

# Start and end day variables
start_day = [z3.Int(f'start_day_{i}') for i in range(7)]
end_day = [z3.Int(f'end_day_{i}') for i in range(7)]

# start_day[0] = 1
solver.add(start_day[0] == 1)

# For i >=1, start_day[i] = end_day[i-1]
for i in range(1, 7):
    solver.add(start_day[i] == end_day[i-1])

# end_day[i] = start_day[i] + duration -1
for i in range(7):
    city_i = cities[i]
    duration_i = durations[city_i]
    solver.add(end_day[i] == start_day[i] + duration_i - 1)

# Barcelona (4) must have day 3 or 4 in its stay
barcelona_event = z3.Or([
    z3.And(
        cities[i] == 4,
        z3.Or(
            z3.And(start_day[i] <= 3, end_day[i] >= 3),
            z3.And(start_day[i] <= 4, end_day[i] >= 4)
        )
    )
    for i in range(7)
])

# Lyon (6) must have day 4 or 5 in its stay
lyon_event = z3.Or([
    z3.And(
        cities[i] == 6,
        z3.Or(
            z3.And(start_day[i] <= 4, end_day[i] >= 4),
            z3.And(start_day[i] <= 5, end_day[i] >= 5)
        )
    )
    for i in range(7)
])

solver.add(barcelona_event)
solver.add(lyon_event)

if solver.check() == z3.sat:
    model = solver.model()
    city_sequence = [model.evaluate(c).as_long() for c in cities]
    start_days = [model.evaluate(s).as_long() for s in start_day]
    end_days = [model.evaluate(e).as_long() for e in end_day]
    
    # Generate itinerary
    itinerary = {}
    city_names = ['Berlin', 'Nice', 'Athens', 'Stockholm', 'Barcelona', 'Vilnius', 'Lyon']
    for i in range(7):
        city_idx = city_sequence[i]
        city_name = city_names[city_idx]
        s_day = start_days[i]
        e_day = end_days[i]
        for day in range(s_day, e_day + 1):
            itinerary[day] = city_name
    
    # Sort the itinerary by day
    sorted_itinerary = sorted(itinerary.items())
    json_output = {'itinerary': [{'day': day, 'city': city} for day, city in sorted_itinerary]]
    
    # Print JSON
    import json
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found")