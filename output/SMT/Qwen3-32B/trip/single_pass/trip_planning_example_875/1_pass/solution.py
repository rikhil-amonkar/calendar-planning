from z3 import *
import json

# Define the cities and their durations
durations = {0: 3, 1: 4, 2: 4, 3: 2, 4: 4, 5: 5, 6: 4}

# Define direct flights
direct_flights = {
    (0, 3), (3, 0),  # Stuttgart and Split
    (3, 2), (2, 3),  # Split and Athens
    (1, 4), (4, 1),  # Edinburgh and Krakow
    (5, 0), (0, 5),  # Venice and Stuttgart
    (4, 0), (0, 4),  # Krakow and Stuttgart
    (1, 0), (0, 1),  # Edinburgh and Stuttgart
    (0, 2), (2, 0),  # Stuttgart and Athens
    (5, 1), (1, 5),  # Venice and Edinburgh
    (2, 6), (6, 2),  # Athens and Mykonos
    (5, 2), (2, 5),  # Venice and Athens
    (0, 3), (3, 0),  # Stuttgart and Split (already included)
    (1, 2), (2, 1),  # Edinburgh and Athens
}

# Create Z3 solver
solver = Solver()

# Define variables for the cities sequence
cities = [Int(f'c{i}') for i in range(7)]
# All distinct
solver.add(Distinct(cities))
# Each city is between 0 and 6
for c in cities:
    solver.add(And(c >= 0, c <= 6))

# Define start_days variables
start_days = [Int(f's{i}') for i in range(7)]
# Constraints for start_days
solver.add(start_days[0] == 1)
for i in range(1, 7):
    prev_city = cities[i-1]
    duration_prev = durations[prev_city]
    solver.add(start_days[i] == start_days[i-1] + duration_prev - 1)

# Constraints for consecutive cities to have direct flights
for i in range(6):
    city_a = cities[i]
    city_b = cities[i+1]
    allowed_pairs = []
    for a, b in direct_flights:
        allowed_pairs.append(And(city_a == a, city_b == b))
    solver.add(Or(allowed_pairs))

# Constraints for specific cities' day ranges
# Stuttgart (0): must include day 11-13
for i in range(7):
    city = cities[i]
    start = start_days[i]
    end = start + durations[0] - 1
    solver.add(Implies(city == 0, And(start <= 13, end >= 11)))

# Split (3): must include day 13-14
for i in range(7):
    city = cities[i]
    start = start_days[i]
    end = start + durations[3] - 1
    solver.add(Implies(city == 3, And(start <= 14, end >= 13)))

# Krakow (4): must include day 8-11
for i in range(7):
    city = cities[i]
    start = start_days[i]
    end = start + durations[4] - 1
    solver.add(Implies(city == 4, And(start <= 11, end >= 8)))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    cities_sequence = [model.eval(c).as_long() for c in cities]
    start_days_sequence = [model.eval(s).as_long() for s in start_days]

    # Generate the itinerary
    city_names = {
        0: 'Stuttgart',
        1: 'Edinburgh',
        2: 'Athens',
        3: 'Split',
        4: 'Krakow',
        5: 'Venice',
        6: 'Mykonos'
    }

    itinerary_dict = {}
    for i in range(7):
        city_code = cities_sequence[i]
        start_day = start_days_sequence[i]
        duration = durations[city_code]
        for day in range(start_day, start_day + duration):
            itinerary_dict[f'day{day}'] = city_names[city_code]

    # Create the JSON-formatted output
    itinerary_list = []
    for day in sorted(itinerary_dict.keys(), key=lambda x: int(x[3:])):
        day_dict = {day: itinerary_dict[day]}
        itinerary_list.append(day_dict)

    result = {'itinerary': itinerary_list}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")