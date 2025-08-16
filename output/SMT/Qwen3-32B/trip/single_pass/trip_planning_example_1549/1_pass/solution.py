import z3
import json

# Define cities and their indices
cities = ['Prague', 'Tallinn', 'Warsaw', 'Porto', 'Naples', 'Milan', 'Lisbon', 'Santorini', 'Riga', 'Stockholm']
durations = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]

# Define allowed flights
pairs = [
    (8, 0), (9, 5), (8, 5), (6, 9), (9, 7), (4, 2), (6, 2), (4, 5), (6, 4),
    (8, 1), (1, 0), (9, 2), (8, 2), (6, 8), (8, 9), (6, 3), (6, 0), (5, 3),
    (0, 5), (6, 5), (2, 3), (2, 1), (7, 5), (9, 0), (9, 1), (2, 5), (7, 4), (2, 0)
]
allowed_flights = set()
for a, b in pairs:
    allowed_flights.add((a, b))
    allowed_flights.add((b, a))

solver = z3.Solver()

# Create variables for the city sequence
city_sequence = [z3.Int(f'city_{i}') for i in range(10)]

# All cities must be distinct and between 0 and 9
solver.add(z3.Distinct(city_sequence))
for c in city_sequence:
    solver.add(z3.And(c >= 0, c <= 9))

# Create variables for start_day and end_day
start_day = [z3.Int(f'start_day_{i}') for i in range(10)]
end_day = [z3.Int(f'end_day_{i}') for i in range(10)]

# Start day of first city is 1
solver.add(start_day[0] == 1)

# For each city in sequence, end_day[i] = start_day[i] + duration - 1
for i in range(10):
    solver.add(end_day[i] == start_day[i] + durations[city_sequence[i]] - 1)

# For consecutive cities, start_day[i+1] = end_day[i]
for i in range(9):
    solver.add(start_day[i+1] == end_day[i])

# End day of last city is 28
solver.add(end_day[9] == 28)

# Constraints for Riga (index 8): start_day <=5 and end_day >=8
riga_index = 8
for i in range(10):
    solver.add(z3.Implies(city_sequence[i] == riga_index, start_day[i] == 5))
    solver.add(z3.Implies(city_sequence[i] == riga_index, end_day[i] == 8))

# Constraints for Tallinn (index 1): start_day >=18 and end_day <=20
tallinn_index = 1
for i in range(10):
    solver.add(z3.Implies(city_sequence[i] == tallinn_index, start_day[i] == 18))
    solver.add(z3.Implies(city_sequence[i] == tallinn_index, end_day[i] == 20))

# Constraints for Milan (index 5): start_day >=24 and end_day <=26
milan_index = 5
for i in range(10):
    solver.add(z3.Implies(city_sequence[i] == milan_index, start_day[i] == 24))
    solver.add(z3.Implies(city_sequence[i] == milan_index, end_day[i] == 26))

# Add flight constraints between consecutive cities
for i in range(9):
    current = city_sequence[i]
    next_c = city_sequence[i+1]
    constraints = []
    for a, b in allowed_flights:
        constraints.append(z3.And(current == a, next_c == b))
    solver.add(z3.Or(*constraints))

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    city_seq = [model.eval(c).as_long() for c in city_sequence]
    start_days = [model.eval(sd).as_long() for sd in start_day]
    end_days = [model.eval(ed).as_long() for ed in end_day]

    itinerary = []
    for day in range(1, 29):
        for i in range(10):
            if start_days[i] <= day <= end_days[i]:
                city_idx = city_seq[i]
                city_name = cities[city_idx]
                itinerary.append({'day': day, 'city': city_name})
                break

    output = {'itinerary': [{'day': entry['day'], 'city': entry['city']} for entry in itinerary]}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")