from z3 import *

# Define cities with indices
cities = {
    'Prague': 0,
    'Warsaw': 1,
    'Dublin': 2,
    'Athens': 3,
    'Vilnius': 4,
    'Porto': 5,
    'London': 6,
    'Seville': 7,
    'Lisbon': 8,
    'Dubrovnik': 9
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Prague']: 3,
    cities['Warsaw']: 4,
    cities['Dublin']: 3,
    cities['Athens']: 3,
    cities['Vilnius']: 4,
    cities['Porto']: 5,
    cities['London']: 3,
    cities['Seville']: 2,
    cities['Lisbon']: 5,
    cities['Dubrovnik']: 3
}

# Allowed direct flights (from, to)
allowed_flights = [
    (1, 4), (4, 1),   # Warsaw <-> Vilnius
    (0, 3), (3, 0),   # Prague <-> Athens
    (6, 8), (8, 6),   # London <-> Lisbon
    (8, 5), (5, 8),   # Lisbon <-> Porto
    (0, 8), (8, 0),   # Prague <-> Lisbon
    (6, 2), (2, 6),   # London <-> Dublin
    (3, 4), (4, 3),   # Athens <-> Vilnius
    (3, 2), (2, 3),   # Athens <-> Dublin
    (0, 6), (6, 0),   # Prague <-> London
    (6, 1), (1, 6),   # London <-> Warsaw
    (2, 7), (7, 2),   # Dublin <-> Seville
    (7, 5), (5, 7),   # Seville <-> Porto
    (8, 3), (3, 8),   # Lisbon <-> Athens
    (2, 5), (5, 2),   # Dublin <-> Porto
    (3, 1), (1, 3),   # Athens <-> Warsaw
    (8, 1), (1, 8),   # Lisbon <-> Warsaw
    (5, 1), (1, 5),   # Porto <-> Warsaw
    (0, 1), (1, 0),   # Prague <-> Warsaw
    (0, 2), (2, 0),   # Prague <-> Dublin
    (3, 9), (9, 3),   # Athens <-> Dubrovnik
    (8, 2), (2, 8),   # Lisbon <-> Dublin
    (9, 2), (2, 9),   # Dubrovnik <-> Dublin
    (8, 7), (7, 8),   # Lisbon <-> Seville
    (6, 3), (3, 6)    # London <-> Athens
]

# Create solver
s = Solver()

# Day variables: 1 to 26 (indices 0-25)
days = [Int(f'day_{i}') for i in range(26)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Prague (days 1-3, indices 0-2)
for i in range(0, 3):
    s.add(days[i] == cities['Prague'])

# Fixed days in Warsaw (days 20-23, indices 19-22)
for i in range(19, 23):
    s.add(days[i] == cities['Warsaw'])

# Fixed days in Porto (days 16-20, indices 15-19)
for i in range(15, 20):
    s.add(days[i] == cities['Porto'])

# Fixed days in London (days 3-5, indices 2-4)
for i in range(2, 5):
    s.add(days[i] == cities['London'])

# Fixed days in Lisbon (days 5-9, indices 4-8)
for i in range(4, 9):
    s.add(days[i] == cities['Lisbon'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 26):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(26):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")