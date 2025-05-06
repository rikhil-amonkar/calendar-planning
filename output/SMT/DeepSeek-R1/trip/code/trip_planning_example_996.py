from z3 import *

# Define cities with indices
cities = {
    'Mykonos': 0,
    'Prague': 1,
    'Valencia': 2,
    'Riga': 3,
    'Zurich': 4,
    'Bucharest': 5,
    'Nice': 6
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Mykonos']: 3,
    cities['Prague']: 3,
    cities['Valencia']: 5,
    cities['Riga']: 5,
    cities['Zurich']: 5,
    cities['Bucharest']: 5,
    cities['Nice']: 2
}

# Allowed direct flights (from, to)
allowed_flights = [
    (0, 6), (6, 0),  # Mykonos <-> Nice
    (0, 4), (4, 0),  # Mykonos <-> Zurich
    (1, 5), (5, 1),  # Prague <-> Bucharest
    (2, 5), (5, 2),  # Valencia <-> Bucharest
    (4, 1), (1, 4),  # Zurich <-> Prague
    (3, 6), (6, 3),  # Riga <-> Nice
    (4, 3), (3, 4),  # Zurich <-> Riga
    (4, 5), (5, 4),  # Zurich <-> Bucharest
    (4, 2), (2, 4),  # Zurich <-> Valencia
    (5, 3), (3, 5),  # Bucharest <-> Riga
    (1, 3), (3, 1),  # Prague <-> Riga
    (1, 2), (2, 1),  # Prague <-> Valencia
    (4, 6), (6, 4)   # Zurich <-> Nice
]

# Create solver
s = Solver()

# Day variables: 1 to 22 (indices 0-21)
days = [Int(f'day_{i}') for i in range(22)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Mykonos (days 1-3, indices 0-2)
for i in range(3):
    s.add(days[i] == cities['Mykonos'])

# Fixed days in Prague (days 7-9, indices 6-8)
for i in range(6, 9):
    s.add(days[i] == cities['Prague'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 22):
    current = days[i]
    prev = days[i-1]
    # Allow staying in the same city or direct flight
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(22):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")