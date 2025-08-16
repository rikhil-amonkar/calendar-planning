import z3
import json

cities = ['Frankfurt', 'Manchester', 'Valencia', 'Naples', 'Oslo', 'Vilnius']
city_to_id = {city: idx for idx, city in enumerate(cities)}
id_to_city = {idx: city for idx, city in enumerate(cities)}

durations = [4, 4, 4, 4, 3, 2]  # Corresponds to the order of cities

direct_flights = [
    ('Valencia', 'Frankfurt'),
    ('Frankfurt', 'Valencia'),
    ('Manchester', 'Frankfurt'),
    ('Frankfurt', 'Manchester'),
    ('Naples', 'Manchester'),
    ('Manchester', 'Naples'),
    ('Naples', 'Frankfurt'),
    ('Frankfurt', 'Naples'),
    ('Naples', 'Oslo'),
    ('Oslo', 'Naples'),
    ('Oslo', 'Frankfurt'),
    ('Frankfurt', 'Oslo'),
    ('Vilnius', 'Frankfurt'),
    ('Frankfurt', 'Vilnius'),
    ('Oslo', 'Vilnius'),
    ('Vilnius', 'Oslo'),
    ('Manchester', 'Oslo'),
    ('Oslo', 'Manchester'),
    ('Valencia', 'Naples'),
    ('Naples', 'Valencia'),
]

allowed_transitions = set()
for a, b in direct_flights:
    allowed_transitions.add((city_to_id[a], city_to_id[b]))

solver = z3.Solver()

# Create variables for the sequence of cities
positions = [z3.Int(f'position_{i}') for i in range(6)]

# All positions are distinct and within 0-5
solver.add([z3.And(0 <= positions[i], positions[i] < 6) for i in range(6)])
solver.add(z3.Distinct(positions))

# Add constraints for direct flights between consecutive positions
for i in range(5):
    current = positions[i]
    next_pos = positions[i + 1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(z3.And(current == a, next_pos == b))
    solver.add(z3.Or(constraints))

# Create start_day variables
start_day = [z3.Int(f'start_day_{i}') for i in range(6)]
solver.add(start_day[0] == 1)

# Add constraints for start_day[i] based on previous start_day and duration
for i in range(1, 6):
    prev_city = positions[i - 1]
    # Compute duration of previous city
    duration_prev = z3.If(prev_city == 0, 4,
                            z3.If(prev_city == 1, 4,
                            z3.If(prev_city == 2, 4,
                            z3.If(prev_city == 3, 4,
                            z3.If(prev_city == 4, 3, 2)))))
    # start_day[i] = start_day[i-1] + duration_prev - 1
    solver.add(start_day[i] == start_day[i - 1] + duration_prev - 1)

# Add constraints for Vilnius (id 5) and Frankfurt (id 0)
for i in range(6):
    # If positions[i] is Vilnius (5), then start_day[i] == 12
    solver.add(z3.Implies(positions[i] == 5, start_day[i] == 12))
    # If positions[i] is Frankfurt (0), then start_day[i] == 13
    solver.add(z3.Implies(positions[i] == 0, start_day[i] == 13))

if solver.check() == z3.sat:
    model = solver.model()
    positions_val = [model.evaluate(p).as_long() for p in positions]
    start_day_val = [model.evaluate(sd).as_long() for sd in start_day]
    sequence = [id_to_city[p] for p in positions_val]
    
    itinerary = {}
    for day in range(1, 17):
        for i in reversed(range(6)):  # Check in reverse order to assign flight day to destination
            city_id = positions_val[i]
            dur = durations[city_id]
            sd = start_day_val[i]
            ed = sd + dur - 1
            if sd <= day <= ed:
                itinerary[day] = id_to_city[city_id]
                break

    output = {'itinerary': [{'day': day, 'city': itinerary[day]} for day in sorted(itinerary.keys())]}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")