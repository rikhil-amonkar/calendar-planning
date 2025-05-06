from z3 import *

# Define cities with indices
cities = {
    'Frankfurt': 0,
    'Salzburg': 1,
    'Athens': 2,
    'Reykjavik': 3,
    'Bucharest': 4,
    'Valencia': 5,
    'Vienna': 6,
    'Amsterdam': 7,
    'Stockholm': 8,
    'Riga': 9
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Frankfurt']: 4,
    cities['Salzburg']: 5,
    cities['Athens']: 5,
    cities['Reykjavik']: 5,
    cities['Bucharest']: 3,
    cities['Valencia']: 2,
    cities['Vienna']: 5,
    cities['Amsterdam']: 3,
    cities['Stockholm']: 3,
    cities['Riga']: 3
}

# Allowed flights (bidirectional and unidirectional)
allowed_flights = [
    # Bidirectional
    (5, 0), (0, 5),   # Valencia <-> Frankfurt
    (6, 4), (4, 6),   # Vienna <-> Bucharest
    (2, 4), (4, 2),   # Athens <-> Bucharest
    (9, 0), (0, 9),   # Riga <-> Frankfurt
    (8, 2), (2, 8),   # Stockholm <-> Athens
    (7, 4), (4, 7),   # Amsterdam <-> Bucharest
    (7, 0), (0, 7),   # Amsterdam <-> Frankfurt
    (8, 6), (6, 8),   # Stockholm <-> Vienna
    (6, 9), (9, 6),   # Vienna <-> Riga
    (7, 3), (3, 7),   # Amsterdam <-> Reykjavik
    (3, 0), (0, 3),   # Reykjavik <-> Frankfurt
    (8, 7), (7, 8),   # Stockholm <-> Amsterdam
    (7, 5), (5, 7),   # Amsterdam <-> Valencia
    (6, 0), (0, 6),   # Vienna <-> Frankfurt
    (5, 4), (4, 5),   # Valencia <-> Bucharest
    (4, 0), (0, 4),   # Bucharest <-> Frankfurt
    (8, 0), (0, 8),   # Stockholm <-> Frankfurt
    (5, 6), (6, 5),   # Valencia <-> Vienna
    (0, 1), (1, 0),   # Frankfurt <-> Salzburg
    (7, 6), (6, 7),   # Amsterdam <-> Vienna
    (8, 3), (3, 8),   # Stockholm <-> Reykjavik
    (7, 9), (9, 7),   # Amsterdam <-> Riga
    (8, 9), (9, 8),   # Stockholm <-> Riga
    (6, 3), (3, 6),   # Vienna <-> Reykjavik
    (7, 2), (2, 7),   # Amsterdam <-> Athens
    (2, 0), (0, 2),   # Athens <-> Frankfurt
    (6, 2), (2, 6),   # Vienna <-> Athens
    (9, 4), (4, 9),   # Riga <-> Bucharest
    # Unidirectional
    (5, 2),           # Valencia -> Athens
    (2, 9),           # Athens -> Riga
    (3, 2)            # Reykjavik -> Athens
]

# Create solver
s = Solver()

# Day variables: 1 to 29 (indices 0-28)
days = [Int(f'day_{i}') for i in range(29)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed constraints
# Stockholm days 1-3 (indices 0-2)
for i in range(3):
    s.add(days[i] == cities['Stockholm'])

# Valencia days 5-6 (indices 4-5)
s.add(days[4] == cities['Valencia'])
s.add(days[5] == cities['Valencia'])

# Vienna days 6-10 (indices 5-9)
for i in range(5, 10):
    s.add(days[i] == cities['Vienna'])

# Athens days 14-18 (indices 13-17)
for i in range(13, 18):
    s.add(days[i] == cities['Athens'])

# Riga days 18-20 (indices 17-19)
for i in range(17, 20):
    s.add(days[i] == cities['Riga'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 29):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(29):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")