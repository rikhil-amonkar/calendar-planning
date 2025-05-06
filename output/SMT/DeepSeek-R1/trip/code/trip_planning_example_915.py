from z3 import *

# Define cities with indices
cities = {
    'Bucharest': 0,
    'Venice': 1,
    'Prague': 2,
    'Frankfurt': 3,
    'Zurich': 4,
    'Florence': 5,
    'Tallinn': 6
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Bucharest']: 3,
    cities['Venice']: 5,
    cities['Prague']: 4,
    cities['Frankfurt']: 5,
    cities['Zurich']: 5,
    cities['Florence']: 5,
    cities['Tallinn']: 5
}

# Allowed direct flights (from, to)
allowed_flights = [
    (2, 6), (6, 2),  # Prague <-> Tallinn
    (2, 4), (4, 2),  # Prague <-> Zurich
    (5, 2), (2, 5),  # Florence <-> Prague
    (3, 0), (0, 3),  # Frankfurt <-> Bucharest
    (3, 1), (1, 3),  # Frankfurt <-> Venice
    (2, 0), (0, 2),  # Prague <-> Bucharest
    (0, 4), (4, 0),  # Bucharest <-> Zurich
    (6, 3), (3, 6),  # Tallinn <-> Frankfurt
    (4, 5),           # Zurich -> Florence
    (3, 4), (4, 3),   # Frankfurt <-> Zurich
    (4, 1), (1, 4),   # Zurich <-> Venice
    (5, 3), (3, 5),   # Florence <-> Frankfurt
    (2, 3), (3, 2),   # Prague <-> Frankfurt
    (6, 4), (4, 6)    # Tallinn <-> Zurich
]

# Create solver
s = Solver()

# Day variables: 1 to 26 (indices 0-25)
days = [Int(f'day_{i}') for i in range(26)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Venice (days 22-26, indices 21-25)
for i in range(21, 26):
    s.add(days[i] == cities['Venice'])

# Fixed days in Frankfurt (days 12-16, indices 11-15)
for i in range(11, 16):
    s.add(days[i] == cities['Frankfurt'])

# Fixed days in Tallinn (days 8-12, indices 7-11)
for i in range(7, 12):
    s.add(days[i] == cities['Tallinn'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 26):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

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