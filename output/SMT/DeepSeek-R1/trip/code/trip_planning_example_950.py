from z3 import *

# Define cities with indices
cities = {
    'Mykonos': 0,
    'Riga': 1,
    'Munich': 2,
    'Bucharest': 3,
    'Rome': 4,
    'Nice': 5,
    'Krakow': 6
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Mykonos']: 3,
    cities['Riga']: 3,
    cities['Munich']: 4,
    cities['Bucharest']: 4,
    cities['Rome']: 4,
    cities['Nice']: 3,
    cities['Krakow']: 2
}

# Allowed flights (bidirectional and unidirectional)
allowed_flights = [
    # Bidirectional
    (5, 1), (1, 5),   # Nice <-> Riga
    (3, 2), (2, 3),   # Bucharest <-> Munich
    (0, 2), (2, 0),   # Mykonos <-> Munich
    (1, 3), (3, 1),   # Riga <-> Bucharest
    (4, 5), (5, 4),   # Rome <-> Nice
    (4, 2), (2, 4),   # Rome <-> Munich
    (0, 5), (5, 0),   # Mykonos <-> Nice
    (4, 0), (0, 4),   # Rome <-> Mykonos
    (2, 6), (6, 2),   # Munich <-> Krakow
    (4, 3), (3, 4),   # Rome <-> Bucharest
    (5, 2), (2, 5),   # Nice <-> Munich
    # Unidirectional
    (1, 2),           # Riga → Munich
    (4, 1)            # Rome → Riga
]

# Create solver
s = Solver()

# Day variables: 1 to 17 (indices 0-16)
days = [Int(f'day_{i}') for i in range(17)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed constraints
# Rome days 1-4 (indices 0-3)
for i in range(4):
    s.add(days[i] == cities['Rome'])

# Mykonos days 4-6 (indices 3-5)
for i in range(3, 6):
    s.add(days[i] == cities['Mykonos'])

# Krakow days 16-17 (indices 15-16)
s.add(days[15] == cities['Krakow'])
s.add(days[16] == cities['Krakow'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 17):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(17):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")