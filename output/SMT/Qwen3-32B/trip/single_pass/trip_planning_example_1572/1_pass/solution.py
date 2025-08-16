from z3 import *
import json

# Define cities and their codes
cities = ['Lyon', 'Paris', 'Riga', 'Berlin', 'Stockholm', 'Zurich', 'Nice', 'Seville', 'Milan', 'Naples']
city_codes = {city: i for i, city in enumerate(cities)}
durations = [3, 5, 2, 2, 3, 5, 2, 3, 3, 4]  # durations for each city in order

# Parse allowed transitions
direct_flights = [
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
allowed_transitions = set()
for a, b in direct_flights:
    allowed_transitions.add((city_codes[a], city_codes[b]))
    allowed_transitions.add((city_codes[b], city_codes[a]))

# Z3 solver
s = Solver()

# Sequence variables
seq = [Int(f'seq_{i}') for i in range(10)]
s.add(Distinct(seq))
for i in range(10):
    s.add(And(seq[i] >= 0, seq[i] <= 9))

# Start_day variables
start_day = [Int(f'start_day_{i}') for i in range(10)]
s.add(start_day[0] == 1)

# Function to get duration of a city code
def get_duration_expr(c):
    return If(c == 0, 3,
        If(c == 1, 5,
        If(c == 2, 2,
        If(c == 3, 2,
        If(c == 4, 3,
        If(c == 5, 5,
        If(c == 6, 2,
        If(c == 7, 3,
        If(c == 8, 3,
        If(c == 9, 4, 0)))))))))

# Constraints for start_day
for i in range(1, 10):
    prev_duration = get_duration_expr(seq[i-1]) - 1
    s.add(start_day[i] == start_day[i-1] + prev_duration)

# Event constraints
for i in range(10):
    # Berlin (code 3)
    s.add(Implies(seq[i] == 3, start_day[i] <= 2))
    # Stockholm (code 4)
    s.add(Implies(seq[i] == 4, And(start_day[i] >= 18, start_day[i] <= 22)))
    # Nice (code 6)
    s.add(Implies(seq[i] == 6, And(start_day[i] >= 11, start_day[i] <= 13)))

# Allowed transitions between consecutive cities
for i in range(9):
    from_code = seq[i]
    to_code = seq[i+1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(And(from_code == a, to_code == b))
    s.add(Or(constraints))

if s.check() == sat:
    m = s.model()
    seq_solution = [m.evaluate(seq[i]).as_long() for i in range(10)]
    start_day_solution = [m.evaluate(start_day[i]).as_long() for i in range(10)]
    end_day_solution = [start_day_solution[i] + durations[seq_solution[i]] - 1 for i in range(10)]

    # Generate day-to-city mapping
    itinerary = []
    for day in range(1, 24):
        for i in range(10):
            if start_day_solution[i] <= day <= end_day_solution[i]:
                city = cities[seq_solution[i]]
                itinerary.append({"day": day, "city": city})
                break

    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")