from z3 import *

# Define cities with indices
cities = {
    'Mykonos': 0,
    'Krakow': 1,
    'Vilnius': 2,
    'Helsinki': 3,
    'Dubrovnik': 4,
    'Oslo': 5,
    'Madrid': 6,
    'Paris': 7
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Mykonos']: 4,
    cities['Krakow']: 5,
    cities['Vilnius']: 2,
    cities['Helsinki']: 2,
    cities['Dubrovnik']: 3,
    cities['Oslo']: 2,
    cities['Madrid']: 5,
    cities['Paris']: 2
}

# Allowed flights (including directionality)
allowed_flights = [
    # Bidirectional flights
    (5, 1), (1, 5),   # Oslo <-> Krakow
    (5, 7), (7, 5),   # Oslo <-> Paris
    (7, 6), (6, 7),   # Paris <-> Madrid
    (3, 2), (2, 3),   # Helsinki <-> Vilnius
    (5, 6), (6, 5),   # Oslo <-> Madrid
    (5, 3), (3, 5),   # Oslo <-> Helsinki
    (3, 1), (1, 3),   # Helsinki <-> Krakow
    (4, 3), (3, 4),   # Dubrovnik <-> Helsinki
    (4, 6), (6, 4),   # Dubrovnik <-> Madrid
    (5, 4), (4, 5),   # Oslo <-> Dubrovnik
    (1, 7), (7, 1),   # Krakow <-> Paris
    (6, 0), (0, 6),   # Madrid <-> Mykonos
    (5, 2), (2, 5),   # Oslo <-> Vilnius
    (3, 7), (7, 3),   # Helsinki <-> Paris
    (2, 7), (7, 2),   # Vilnius <-> Paris
    (3, 6), (6, 3),   # Helsinki <-> Madrid
    # Unidirectional flight (Krakow -> Vilnius)
    (1, 2)
]

# Create solver
s = Solver()

# Day variables: 1 to 18 (indices 0-17)
days = [Int(f'day_{i}') for i in range(18)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Oslo (days 1-2, indices 0-1)
s.add(days[0] == cities['Oslo'])
s.add(days[1] == cities['Oslo'])

# Fixed days in Dubrovnik (days 2-4, indices 1-3)
s.add(days[1] == cities['Dubrovnik'])
s.add(days[2] == cities['Dubrovnik'])
s.add(days[3] == cities['Dubrovnik'])

# Fixed days in Mykonos (days 15-18, indices 14-17)
for i in range(14, 18):
    s.add(days[i] == cities['Mykonos'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 18):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(18):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")