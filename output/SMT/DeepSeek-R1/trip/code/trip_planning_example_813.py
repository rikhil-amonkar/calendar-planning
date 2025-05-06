from z3 import *

# Define cities with indices
cities = {
    'Seville': 0,
    'Vilnius': 1,
    'Santorini': 2,
    'London': 3,
    'Stuttgart': 4,
    'Dublin': 5,
    'Frankfurt': 6
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Seville']: 5,
    cities['Vilnius']: 3,
    cities['Santorini']: 2,
    cities['London']: 2,
    cities['Stuttgart']: 3,
    cities['Dublin']: 3,
    cities['Frankfurt']: 5
}

# Allowed direct flights (from, to)
allowed_flights = [
    (6, 5), (5, 6),   # Frankfurt <-> Dublin
    (6, 3), (3, 6),   # Frankfurt <-> London
    (3, 5), (5, 3),   # London <-> Dublin
    (1, 6), (6, 1),   # Vilnius <-> Frankfurt
    (6, 4), (4, 6),   # Frankfurt <-> Stuttgart
    (5, 0), (0, 5),   # Dublin <-> Seville
    (3, 2), (2, 3),   # London <-> Santorini
    (4, 3), (3, 4),   # Stuttgart <-> London
    (2, 5), (5, 2)    # Santorini <-> Dublin
]

# Create solver
s = Solver()

# Day variables: 1 to 17 (indices 0-16)
days = [Int(f'day_{i}') for i in range(17)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in London (days 9-10, indices 8-9)
s.add(days[8] == cities['London'])
s.add(days[9] == cities['London'])

# Stuttgart must be between day 7-9 (indices 6-8)
for i in range(17):
    s.add(Implies(days[i] == cities['Stuttgart'], And(i >= 6, i <= 8)))

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