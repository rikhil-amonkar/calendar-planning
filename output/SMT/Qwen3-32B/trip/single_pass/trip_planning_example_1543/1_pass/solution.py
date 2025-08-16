from z3 import *
import json

cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
city_to_index = {city: i for i, city in enumerate(cities)}

direct_flights = {
    ('Warsaw', 'Vilnius'), ('Prague', 'Athens'), ('London', 'Lisbon'), ('Lisbon', 'Porto'), 
    ('Prague', 'Lisbon'), ('London', 'Dublin'), ('Athens', 'Vilnius'), ('Athens', 'Dublin'), 
    ('Prague', 'London'), ('London', 'Warsaw'), ('Dublin', 'Seville'), ('Seville', 'Porto'), 
    ('Lisbon', 'Athens'), ('Dublin', 'Porto'), ('Athens', 'Warsaw'), ('Lisbon', 'Warsaw'), 
    ('Porto', 'Warsaw'), ('Prague', 'Warsaw'), ('Prague', 'Dublin'), ('Athens', 'Dubrovnik'), 
    ('Lisbon', 'Dublin'), ('Dubrovnik', 'Dublin'), ('Lisbon', 'Seville'), ('London', 'Athens')
}

allowed_transitions = set()
for (a, b) in direct_flights:
    a_idx = city_to_index[a]
    b_idx = city_to_index[b]
    allowed_transitions.add((a_idx, b_idx))
    allowed_transitions.add((b_idx, a_idx))  # since flights are bidirectional

durations = {
    'Prague': 3,
    'Warsaw': 4,
    'Dublin': 3,
    'Athens': 3,
    'Vilnius': 4,
    'Porto': 5,
    'London': 3,
    'Seville': 2,
    'Lisbon': 5,
    'Dubrovnik': 3
}

event_constraints = {
    'Prague': (1, 3),
    'London': (3, 5),
    'Lisbon': (5, 9),
    'Porto': (16, 20),
    'Warsaw': (20, 23)
}

s = Solver()

# Define the sequence of cities
seq = [Int('seq_%d' % i) for i in range(10)]
s.add(Distinct(seq))
for i in range(10):
    s.add(And(seq[i] >= 0, seq[i] <= 9))

# Define start and end for each city in the sequence
start = [Int('start_%d' % i) for i in range(10)]
end = [Int('end_%d' % i) for i in range(10)]

# Duration constraints
for i in range(10):
    duration = 0
    for j in range(10):
        duration += If(seq[i] == j, durations[cities[j]], 0)
    s.add(end[i] == start[i] + duration - 1)

# Consecutive start and end
for i in range(9):
    s.add(start[i+1] == end[i])

# Last end is 26
s.add(end[9] == 26)

# Event constraints
for city_j in range(10):
    city_name = cities[city_j]
    if city_name in event_constraints:
        event_start, event_end = event_constraints[city_name]
        for i in range(10):
            s.add(Implies(seq[i] == city_j, start[i] <= event_start))
            s.add(Implies(seq[i] == city_j, end[i] >= event_end))

# Direct flight constraints between consecutive cities
for i in range(9):
    constraints = []
    for (a, b) in allowed_transitions:
        constraints.append(And(seq[i] == a, seq[i+1] == b))
    s.add(Or(constraints))

if s.check() == sat:
    m = s.model()
    # Extract the sequence
    sequence = [m.evaluate(seq[i]) for i in range(10)]
    # Convert to city names
    city_sequence = [cities[sequence[i]] for i in range(10)]
    # Extract start and end days
    start_days = [m.evaluate(start[i]).as_long() for i in range(10)]
    end_days = [m.evaluate(end[i]).as_long() for i in range(10)]
    # Now build the day-city mapping
    itinerary = {}
    for i in range(10):
        city = city_sequence[i]
        s_day = start_days[i]
        e_day = end_days[i]
        for day in range(s_day, e_day + 1):
            itinerary[day] = city
    # Print the itinerary as JSON
    sorted_days = sorted(itinerary.keys())
    result = {'itinerary': [{'day': day, 'city': itinerary[day]} for day in sorted_days]}
    print(json.dumps(result))
else:
    print("No solution found.")