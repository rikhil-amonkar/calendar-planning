from z3 import *

# Define cities with indices
cities = {
    'Oslo': 0,
    'Helsinki': 1,
    'Edinburgh': 2,
    'Riga': 3,
    'Tallinn': 4,
    'Budapest': 5,
    'Vilnius': 6,
    'Porto': 7,
    'Geneva': 8
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Oslo']: 2,
    cities['Helsinki']: 2,
    cities['Edinburgh']: 3,
    cities['Riga']: 2,
    cities['Tallinn']: 5,
    cities['Budapest']: 5,
    cities['Vilnius']: 5,
    cities['Porto']: 5,
    cities['Geneva']: 4
}

# Allowed flights (bidirectional and unidirectional)
allowed_flights = [
    # Bidirectional
    (7, 0), (0, 7),   # Porto <-> Oslo
    (2, 5), (5, 2),   # Edinburgh <-> Budapest
    (2, 8), (8, 2),   # Edinburgh <-> Geneva
    (2, 7), (7, 2),   # Edinburgh <-> Porto
    (6, 1), (1, 6),   # Vilnius <-> Helsinki
    (3, 0), (0, 3),   # Riga <-> Oslo
    (8, 0), (0, 8),   # Geneva <-> Oslo
    (2, 0), (0, 2),   # Edinburgh <-> Oslo
    (2, 1), (1, 2),   # Edinburgh <-> Helsinki
    (6, 0), (0, 6),   # Vilnius <-> Oslo
    (3, 1), (1, 3),   # Riga <-> Helsinki
    (5, 8), (8, 5),   # Budapest <-> Geneva
    (1, 5), (5, 1),   # Helsinki <-> Budapest
    (1, 0), (0, 1),   # Helsinki <-> Oslo
    (2, 3), (3, 2),   # Edinburgh <-> Riga
    (4, 1), (1, 4),   # Tallinn <-> Helsinki
    (8, 7), (7, 8),   # Geneva <-> Porto
    (5, 0), (0, 5),   # Budapest <-> Oslo
    (1, 8), (8, 1),   # Helsinki <-> Geneva
    (4, 0), (0, 4),   # Tallinn <-> Oslo
    # Unidirectional
    (3, 4),           # Riga → Tallinn
    (4, 6),           # Tallinn → Vilnius
    (3, 6)            # Riga → Vilnius
]

# Create solver
s = Solver()

# Day variables: 1 to 25 (indices 0-24)
days = [Int(f'day_{i}') for i in range(25)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Oslo (days 24-25, indices 23-24)
s.add(days[23] == cities['Oslo'])
s.add(days[24] == cities['Oslo'])

# Fixed days in Tallinn (days 4-8, indices 3-7)
for i in range(3, 8):
    s.add(days[i] == cities['Tallinn'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 25):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

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