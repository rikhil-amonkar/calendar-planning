from z3 import *

# Define cities with indices
cities = {
    'Paris': 0,
    'Warsaw': 1,
    'Krakow': 2,
    'Tallinn': 3,
    'Riga': 4,
    'Copenhagen': 5,
    'Helsinki': 6,
    'Oslo': 7,
    'Santorini': 8,
    'Lyon': 9
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Paris']: 5,
    cities['Warsaw']: 2,
    cities['Krakow']: 2,
    cities['Tallinn']: 2,
    cities['Riga']: 2,
    cities['Copenhagen']: 5,
    cities['Helsinki']: 5,
    cities['Oslo']: 5,
    cities['Santorini']: 2,
    cities['Lyon']: 4
}

# Allowed direct flights (from, to)
allowed_flights = [
    (1, 4), (4, 1),   # Warsaw <-> Riga
    (1, 3), (3, 1),   # Warsaw <-> Tallinn
    (5, 6), (6, 5),   # Copenhagen <-> Helsinki
    (9, 0), (0, 9),   # Lyon <-> Paris
    (5, 1), (1, 5),   # Copenhagen <-> Warsaw
    (9, 7), (7, 9),   # Lyon <-> Oslo
    (0, 7), (7, 0),   # Paris <-> Oslo
    (0, 4), (4, 0),   # Paris <-> Riga
    (2, 6), (6, 2),   # Krakow <-> Helsinki
    (0, 3), (3, 0),   # Paris <-> Tallinn
    (7, 4), (4, 7),   # Oslo <-> Riga
    (2, 1), (1, 2),   # Krakow <-> Warsaw
    (0, 6), (6, 0),   # Paris <-> Helsinki
    (5, 8), (8, 5),   # Copenhagen <-> Santorini
    (6, 1), (1, 6),   # Helsinki <-> Warsaw
    (6, 4), (4, 6),   # Helsinki <-> Riga
    (5, 2), (2, 5),   # Copenhagen <-> Krakow
    (5, 4), (4, 5),   # Copenhagen <-> Riga
    (0, 2), (2, 0),   # Paris <-> Krakow
    (5, 7), (7, 5),   # Copenhagen <-> Oslo
    (7, 3), (3, 7),   # Oslo <-> Tallinn
    (7, 6), (6, 7),   # Oslo <-> Helsinki
    (5, 3), (3, 5),   # Copenhagen <-> Tallinn
    (7, 2), (2, 7),   # Oslo <-> Krakow
    (4, 3),           # Riga -> Tallinn (one-way)
    (6, 3), (3, 6),   # Helsinki <-> Tallinn
    (0, 5), (5, 0),   # Paris <-> Copenhagen
    (0, 1), (1, 0),   # Paris <-> Warsaw
    (8, 7),           # Santorini -> Oslo (one-way)
    (7, 1), (1, 7)    # Oslo <-> Warsaw
]

# Create solver
s = Solver()

# Day variables: 1 to 25 (indices 0-24)
days = [Int(f'day_{i}') for i in range(25)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Paris (days 4-8, indices 3-7)
for i in range(3, 8):
    s.add(days[i] == cities['Paris'])

# Fixed days in Krakow (days 17-18, indices 16-17)
s.add(days[16] == cities['Krakow'])
s.add(days[17] == cities['Krakow'])

# Fixed days in Riga (days 23-24, indices 22-23)
s.add(days[22] == cities['Riga'])
s.add(days[23] == cities['Riga'])

# Fixed days in Santorini (days 12-13, indices 11-12)
s.add(days[11] == cities['Santorini'])
s.add(days[12] == cities['Santorini'])

# Helsinki must be visited at least one day between days 18-22 (indices 17-21)
helsinki_in_period = [days[i] == cities['Helsinki'] for i in range(17, 22)]
s.add(Sum([If(cond, 1, 0) for cond in helsinki_in_period]) >= 1)

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 25):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights]))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(25):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")