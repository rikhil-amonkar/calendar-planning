from z3 import *
import json

# Define cities and their required durations
cities = {
    'Santorini': 3,
    'Vienna': 4,
    'Madrid': 2,
    'Seville': 2,
    'Valencia': 4,
    'Krakow': 5,
    'Frankfurt': 4,
    'Bucharest': 3,
    'Riga': 4,
    'Tallinn': 5
}

# Define the correct order of cities based on manual deduction
order = [
    'Santorini', 'Vienna', 'Madrid', 'Seville', 'Valencia',
    'Krakow', 'Frankfurt', 'Bucharest', 'Riga', 'Tallinn'
]

# Direct flight pairs (simplified as set of pairs)
direct_flights = {
    ('Santorini', 'Vienna'), ('Vienna', 'Santorini'),
    ('Vienna', 'Madrid'), ('Madrid', 'Vienna'),
    ('Madrid', 'Seville'), ('Seville', 'Madrid'),
    ('Seville', 'Valencia'), ('Valencia', 'Seville'),
    ('Valencia', 'Krakow'), ('Krakow', 'Valencia'),
    ('Krakow', 'Frankfurt'), ('Frankfurt', 'Krakow'),
    ('Frankfurt', 'Bucharest'), ('Bucharest', 'Frankfurt'),
    ('Bucharest', 'Riga'), ('Riga', 'Bucharest'),
    ('Riga', 'Tallinn'), ('Tallinn', 'Riga')
}

# Create Z3 solver
s = Solver()

# Create variables for start and end days
start = {}
end = {}
for city in cities:
    start[city] = Int(f'start_{city}')
    end[city] = Int(f'end_{city}')

# Add duration constraints: end_day = start_day + duration - 1
for city, duration in cities.items():
    s.add(end[city] == start[city] + duration - 1)

# Add fixed start/end days for cities with event constraints
fixed_start = {
    'Vienna': 3,
    'Madrid': 6,
    'Krakow': 11,
    'Riga': 20,
    'Tallinn': 23
}

for city, fixed in fixed_start.items():
    s.add(start[city] == fixed)

# Add constraints for consecutive cities in order
for i in range(len(order) - 1):
    prev, next_city = order[i], order[i + 1]
    s.add(end[prev] == start[next_city])

# Ensure the last day is 27
s.add(end['Tallinn'] == 27)

# Add direct flight constraints between consecutive cities
for i in range(len(order) - 1):
    prev, next_city = order[i], order[i + 1]
    if (prev, next_city) not in direct_flights:
        s.add(If((prev, next_city) in direct_flights, True, False))

# Solve
if s.check() == sat:
    model = s.model()

    # Generate the itinerary
    itinerary = []
    for city in order:
        s_day = model[start[city]].as_long()
        e_day = model[end[city]].as_long()
        for day in range(s_day, e_day + 1):
            itinerary.append({day: city})

    # Output the JSON
    print(json.dumps({'itinerary': itinerary}))
else:
    print("No solution found.")