from z3 import *

# Define cities with indices
cities = {
    'Reykjavik': 0,
    'Stockholm': 1,
    'Porto': 2,
    'Nice': 3,
    'Venice': 4,
    'Vienna': 5,
    'Split': 6,
    'Copenhagen': 7
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Reykjavik']: 2,
    cities['Stockholm']: 2,
    cities['Porto']: 5,
    cities['Nice']: 3,
    cities['Venice']: 4,
    cities['Vienna']: 3,
    cities['Split']: 3,
    cities['Copenhagen']: 2
}

# Allowed direct flights (from, to)
allowed_flights = [
    (7, 5), (5, 7),   # Copenhagen <-> Vienna
    (3, 1), (1, 3),   # Nice <-> Stockholm
    (6, 7), (7, 6),   # Split <-> Copenhagen
    (3, 0), (0, 3),   # Nice <-> Reykjavik
    (3, 2), (2, 3),   # Nice <-> Porto
    (0, 5), (5, 0),   # Reykjavik <-> Vienna
    (1, 7), (7, 1),   # Stockholm <-> Copenhagen
    (3, 4), (4, 3),   # Nice <-> Venice
    (3, 5), (5, 3),   # Nice <-> Vienna
    (0, 7), (7, 0),   # Reykjavik <-> Copenhagen
    (3, 7), (7, 3),   # Nice <-> Copenhagen
    (1, 5), (5, 1),   # Stockholm <-> Vienna
    (4, 5), (5, 4),   # Venice <-> Vienna
    (7, 2), (2, 7),   # Copenhagen <-> Porto
    (0, 1), (1, 0),   # Reykjavik <-> Stockholm
    (1, 6), (6, 1),   # Stockholm <-> Split
    (6, 5), (5, 6),   # Split <-> Vienna
    (7, 4), (4, 7),   # Copenhagen <-> Venice
    (5, 2), (2, 5)    # Vienna <-> Porto
]

# Create solver
s = Solver()

# Day variables: 1 to 17 (indices 0-16)
days = [Int(f'day_{i}') for i in range(17)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Reykjavik (days 3-4, indices 2-3)
for i in range(2, 4):
    s.add(days[i] == cities['Reykjavik'])

# Fixed days in Stockholm (days 4-5, indices 3-4)
for i in range(3, 5):
    s.add(days[i] == cities['Stockholm'])

# Fixed days in Porto (days 13-17, indices 12-16)
for i in range(12, 17):
    s.add(days[i] == cities['Porto'])

# Fixed days in Vienna (days 11-13, indices 10-12)
for i in range(10, 13):
    s.add(days[i] == cities['Vienna'])

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