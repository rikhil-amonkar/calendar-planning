from z3 import *
import json

# Define cities and their required durations
cities = ['Warsaw', 'Venice', 'Vilnius', 'Salzburg', 'Amsterdam', 'Barcelona', 'Paris', 'Hamburg', 'Florence', 'Tallinn']
durations = {
    'Warsaw': 4,
    'Venice': 3,
    'Vilnius': 3,
    'Salzburg': 4,
    'Amsterdam': 2,
    'Barcelona': 5,
    'Paris': 2,
    'Hamburg': 4,
    'Florence': 5,
    'Tallinn': 2
}
events = {
    'Paris': {'start': 1, 'end': 2},
    'Barcelona': {'start': 2, 'end': 6},
    'Salzburg': {'start': 22, 'end': 25},
    'Hamburg': {'start': 19, 'end': 22},
    'Tallinn': {'start': 11, 'end': 12}
}

# Direct flights
direct_flights = [
    ('Paris', 'Venice'), ('Barcelona', 'Amsterdam'), ('Amsterdam', 'Warsaw'),
    ('Amsterdam', 'Vilnius'), ('Barcelona', 'Warsaw'), ('Warsaw', 'Venice'),
    ('Amsterdam', 'Hamburg'), ('Barcelona', 'Hamburg'), ('Barcelona', 'Florence'),
    ('Barcelona', 'Venice'), ('Paris', 'Hamburg'), ('Paris', 'Vilnius'),
    ('Paris', 'Amsterdam'), ('Paris', 'Florence'), ('Florence', 'Amsterdam'),
    ('Vilnius', 'Warsaw'), ('Barcelona', 'Tallinn'), ('Paris', 'Warsaw'),
    ('Tallinn', 'Warsaw'), ('Tallinn', 'Vilnius'), ('Amsterdam', 'Tallinn'),
    ('Paris', 'Tallinn'), ('Paris', 'Barcelona'), ('Venice', 'Hamburg'),
    ('Warsaw', 'Hamburg'), ('Hamburg', 'Salzburg')
]

direct_flights_set = {frozenset(pair) for pair in direct_flights}

# Generate allowed_pairs for transitions
allowed_pairs = []
for a in range(10):
    for b in range(10):
        city_a = cities[a]
        city_b = cities[b]
        if frozenset({city_a, city_b}) in direct_flights_set:
            allowed_pairs.append((a, b))

# Z3 setup
solver = Solver()

# Sequence variables
seq = [Int('seq_{}'.format(i)) for i in range(10)]
for i in range(10):
    solver.add(seq[i] >= 0)
    solver.add(seq[i] <= 9)
solver.add(Distinct(seq))

# Start and end day variables
start_day = [Int('start_day_{}'.format(i)) for i in range(10)]
end_day = [Int('end_day_{}'.format(i)) for i in range(10)]

# Duration array
durations_list = [durations[city] for city in cities]
durations_array = Array('durations_array', IntSort(), IntSort())
for i in range(10):
    solver.add(durations_array[i] == durations_list[i])

# End day constraints
for j in range(10):
    solver.add(end_day[j] == start_day[j] + (durations_array[seq[j]] - 1))

# First day and last day constraints
solver.add(start_day[0] == 1)
solver.add(end_day[9] == 25)

# Transition constraints
for i in range(9):
    constraints = []
    for (a, b) in allowed_pairs:
        constraints.append(And(seq[i] == a, seq[i+1] == b))
    solver.add(Or(constraints))

# Event constraints
for j in range(10):
    for i in range(10):
        city = cities[i]
        if city in events:
            if city == 'Paris':
                constraint = start_day[j] == 1
            elif city == 'Barcelona':
                constraint = start_day[j] <= 6
            elif city == 'Salzburg':
                constraint = And(start_day[j] >= 19, start_day[j] <= 22)
            elif city == 'Hamburg':
                constraint = And(start_day[j] >= 16, start_day[j] <= 19)
            elif city == 'Tallinn':
                constraint = And(start_day[j] >= 10, start_day[j] <= 12)
            else:
                constraint = True
            solver.add(Implies(seq[j] == i, constraint))

# Solve
if solver.check() == sat:
    model = solver.model()
    seq_values = [model.evaluate(seq[i]).as_long() for i in range(10)]
    start_day_values = [model.evaluate(start_day[i]).as_long() for i in range(10)]
    end_day_values = [model.evaluate(end_day[i]).as_long() for i in range(10)]
    itinerary = []
    for i in range(10):
        city = cities[seq_values[i]]
        start = start_day_values[i]
        end = end_day_values[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))