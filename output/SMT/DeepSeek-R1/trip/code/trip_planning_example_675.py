from z3 import *

# Define cities with indices
cities = {
    'Dubrovnik': 0,
    'Split': 1,
    'Milan': 2,
    'Porto': 3,
    'Krakow': 4,
    'Munich': 5
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Dubrovnik']: 4,
    cities['Split']: 3,
    cities['Milan']: 3,
    cities['Porto']: 4,
    cities['Krakow']: 2,
    cities['Munich']: 5
}

# Allowed direct flights (from, to)
allowed_flights = [
    (5, 3), (3, 5),   # Munich <-> Porto
    (1, 2), (2, 1),   # Split <-> Milan
    (2, 3), (3, 2),   # Milan <-> Porto
    (5, 4), (4, 5),   # Munich <-> Krakow
    (5, 2), (2, 5),   # Munich <-> Milan
    (0, 5), (5, 0),   # Dubrovnik <-> Munich
    (4, 1), (1, 4),   # Krakow <-> Split
    (4, 2), (2, 4),   # Krakow <-> Milan
    (5, 1), (1, 5)    # Munich <-> Split
]

# Create solver
s = Solver()

# Day variables: 1 to 16 (indices 0-15)
days = [Int(f'day_{i}') for i in range(16)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Munich (days 4-8, indices 3-7)
for i in range(3, 8):
    s.add(days[i] == cities['Munich'])

# Fixed days in Milan (days 11-13, indices 10-12)
for i in range(10, 13):
    s.add(days[i] == cities['Milan'])

# Fixed days in Krakow (days 8-9, indices 7-8)
s.add(days[7] == cities['Krakow'])
s.add(days[8] == cities['Krakow'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 16):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights]))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(16):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")