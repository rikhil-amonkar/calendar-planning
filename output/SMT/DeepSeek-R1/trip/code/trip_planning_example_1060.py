from z3 import *

# Define cities with indices
cities = {
    'Reykjavik': 0,
    'Stuttgart': 1,
    'Istanbul': 2,
    'Vilnius': 3,
    'Seville': 4,
    'Geneva': 5,
    'Valencia': 6,
    'Munich': 7
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Reykjavik']: 4,
    cities['Stuttgart']: 4,
    cities['Istanbul']: 4,
    cities['Vilnius']: 4,
    cities['Seville']: 3,
    cities['Geneva']: 5,
    cities['Valencia']: 5,
    cities['Munich']: 3
}

# Allowed direct flights (from, to)
allowed_flights = [
    # Geneva and Istanbul
    (5, 2), (2, 5),
    # Reykjavik and Munich
    (0, 7), (7, 0),
    # Stuttgart and Valencia
    (1, 6), (6, 1),
    # From Reykjavik to Stuttgart
    (0, 1),
    # Stuttgart and Istanbul
    (1, 2), (2, 1),
    # Munich and Geneva
    (7, 5), (5, 7),
    # Istanbul and Vilnius
    (2, 3), (3, 2),
    # Valencia and Seville
    (6, 4), (4, 6),
    # Valencia and Istanbul
    (6, 2), (2, 6),
    # From Vilnius to Munich
    (3, 7),
    # Seville and Munich
    (4, 7), (7, 4),
    # Munich and Istanbul
    (7, 2), (2, 7),
    # Valencia and Geneva
    (6, 5), (5, 6),
    # Valencia and Munich
    (6, 7), (7, 6)
]

# Create solver
s = Solver()

# Day variables: 1 to 25
days = [Int(f'day_{i}') for i in range(1, 26)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days
# Reykjavik days 1-4
for i in range(0, 4):
    s.add(days[i] == cities['Reykjavik'])
# Munich days 13-15
for i in range(12, 15):
    s.add(days[i] == cities['Munich'])
# Istanbul days 19-22 (indices 18-21)
for i in range(18, 22):
    s.add(days[i] == cities['Istanbul'])

# Stuttgart must be on day 4 and 7 (indices 3 and 6)
s.add(days[3] == cities['Stuttgart'])  # day4
s.add(days[6] == cities['Stuttgart'])  # day7

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 25):
    current = days[i]
    prev = days[i-1]
    # Allow staying in the same city
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

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