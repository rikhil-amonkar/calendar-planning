from z3 import *

# Define cities with indices
cities = {
    'Porto': 0,
    'Prague': 1,
    'Reykjavik': 2,
    'Santorini': 3,
    'Amsterdam': 4,
    'Munich': 5
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Porto']: 5,
    cities['Prague']: 4,
    cities['Reykjavik']: 4,
    cities['Santorini']: 2,
    cities['Amsterdam']: 2,
    cities['Munich']: 4
}

# Allowed direct flights (from, to)
allowed_flights = [
    (0, 4), (4, 0),   # Porto <-> Amsterdam
    (5, 4), (4, 5),   # Munich <-> Amsterdam
    (2, 4), (4, 2),   # Reykjavik <-> Amsterdam
    (5, 0), (0, 5),   # Munich <-> Porto
    (1, 2), (2, 1),   # Prague <-> Reykjavik
    (2, 5), (5, 2),   # Reykjavik <-> Munich
    (4, 3), (3, 4),   # Amsterdam <-> Santorini
    (1, 4), (4, 1),   # Prague <-> Amsterdam
    (1, 5), (5, 1)    # Prague <-> Munich
]

# Create solver
s = Solver()

# Day variables: 1 to 16 (indices 0-15)
days = [Int(f'day_{i}') for i in range(16)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Reykjavik (days 4-7, indices 3-6)
for i in range(3, 7):
    s.add(days[i] == cities['Reykjavik'])

# Fixed days in Amsterdam (days 14-15, indices 13-14)
s.add(days[13] == cities['Amsterdam'])
s.add(days[14] == cities['Amsterdam'])

# Fixed days in Munich (days 7-10, indices 6-9)
for i in range(6, 10):
    s.add(days[i] == cities['Munich'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 16):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

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