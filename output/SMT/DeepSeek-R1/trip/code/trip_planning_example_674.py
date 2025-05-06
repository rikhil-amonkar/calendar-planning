from z3 import *

# Define cities with indices
cities = {
    'Helsinki': 0,
    'Warsaw': 1,
    'Madrid': 2,
    'Split': 3,
    'Reykjavik': 4,
    'Budapest': 5
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Helsinki']: 2,
    cities['Warsaw']: 3,
    cities['Madrid']: 4,
    cities['Split']: 4,
    cities['Reykjavik']: 2,
    cities['Budapest']: 4
}

# Allowed direct flights (from, to)
allowed_flights = [
    (0, 4), (4, 0),   # Helsinki <-> Reykjavik
    (5, 1), (1, 5),   # Budapest <-> Warsaw
    (2, 3), (3, 2),   # Madrid <-> Split
    (0, 3), (3, 0),   # Helsinki <-> Split
    (0, 2), (2, 0),   # Helsinki <-> Madrid
    (0, 5), (5, 0),   # Helsinki <-> Budapest
    (4, 1), (1, 4),   # Reykjavik <-> Warsaw
    (0, 1), (1, 0),   # Helsinki <-> Warsaw
    (2, 5), (5, 2),   # Madrid <-> Budapest
    (5, 4), (4, 5),   # Budapest <-> Reykjavik
    (2, 1), (1, 2),   # Madrid <-> Warsaw
    (1, 3), (3, 1),   # Warsaw <-> Split
    (4, 2)            # Reykjavik -> Madrid (one-way)
]

# Create solver
s = Solver()

# Day variables: 1 to 14 (indices 0-13)
days = [Int(f'day_{i}') for i in range(14)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Helsinki (days 1-2, indices 0-1)
s.add(days[0] == cities['Helsinki'])
s.add(days[1] == cities['Helsinki'])

# Fixed days in Reykjavik (days 8-9, indices 7-8)
s.add(days[7] == cities['Reykjavik'])
s.add(days[8] == cities['Reykjavik'])

# Fixed days in Warsaw (days 9-11, indices 8-10)
s.add(days[8] == cities['Warsaw'])
s.add(days[9] == cities['Warsaw'])
s.add(days[10] == cities['Warsaw'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 14):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(14):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")