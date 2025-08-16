import z3
from z3 import *
import json

# Define city codes
cities = {
    'Bucharest': 0,
    'Krakow': 1,
    'Munich': 2,
    'Barcelona': 3,
    'Warsaw': 4,
    'Budapest': 5,
    'Stockholm': 6,
    'Riga': 7,
    'Edinburgh': 8,
    'Vienna': 9
}

required_days = {
    0: 2,   # Bucharest
    1: 4,   # Krakow
    2: 3,   # Munich
    3: 5,   # Barcelona
    4: 5,   # Warsaw
    5: 5,   # Budapest
    6: 2,   # Stockholm
    7: 5,   # Riga
    8: 5,   # Edinburgh
    9: 5    # Vienna
}

# Build allowed_flights
allowed_flights = set()
direct_flights_list = [
    (5,2), (0,7), (2,1), (2,4), (2,0), (8,6), (3,4), (8,1), (3,2), (6,1),
    (5,9), (3,7), (8,5), (3,1), (7,2), (9,0), (5,4), (9,4), (3,9), (5,0),
    (9,2), (7,4), (6,7), (6,4)
]
for a, b in direct_flights_list:
    allowed_flights.add((a, b))
    allowed_flights.add((b, a))

# Create Z3 variables for each day (1-32)
solver = Solver()
day_city = [Int(f'day_{i}') for i in range(1, 33)]  # days 1 to 32 are indices 0 to 31 in this list

# Add constraints that each day's city is between 0 and 9
for d in day_city:
    solver.add(And(d >= 0, d <= 9))

# Add constraints for consecutive days' flights
for i in range(31):  # i from 0 to 30 (days 1 to 31)
    current_day = day_city[i]
    next_day = day_city[i+1]
    allowed_pairs = [And(current_day == a, next_day == b) for a, b in allowed_flights]
    cond = Or(allowed_pairs)
    solver.add(Implies(current_day != next_day, cond))

# Add constraints for required days in each city
for city in range(10):
    required = required_days[city]
    itinerary_count = Sum([If(day_city[i] == city, 1, 0) for i in range(32)])
    allowed_D = [d for d in range(10) if (d, city) in allowed_flights]
    arrival_count = 0
    for x in range(31):  # X is 0 to 30 (days 1 to 31)
        cond = And(
            day_city[x+1] == city,
            day_city[x] != city,
            Or([day_city[x] == d for d in allowed_D])
        )
        arrival_count += If(cond, 1, 0)
    solver.add(itinerary_count + arrival_count == required)

# Add event constraints
events = [
    (2, [18, 19, 20]),  # Munich days 18-20
    (4, [25, 29]),       # Warsaw days 25 and 29
    (5, list(range(9, 14))),  # Budapest days 9-13
    (6, [17, 18]),        # Stockholm days 17-18
    (8, list(range(1, 6)))  # Edinburgh days 1-5
]

for city, days in events:
    conditions = []
    for d in days:
        if d < 1 or d > 32:
            continue
        part1 = (day_city[d-1] == city)
        if d < 32:
            allowed_D = [D for D in range(10) if (D, city) in allowed_flights]
            part2 = And(
                day_city[d] == city,
                Or([day_city[d-1] == D for D in allowed_D])
            )
            cond = Or(part1, part2)
        else:
            cond = part1
        conditions.append(cond)
    if conditions:
        solver.add(Or(conditions))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(32):
        city_code = model[day_city[i]].as_long()
        city_name = [k for k, v in cities.items() if v == city_code][0]
        itinerary.append({'day': i+1, 'city': city_name})
    result = {'itinerary': [{'day': entry['day'], 'city': entry['city']} for entry in itinerary]}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")