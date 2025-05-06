from z3 import *

# Define cities with indices
cities = {
    'Stuttgart': 0,
    'Manchester': 1,
    'Madrid': 2,
    'Vienna': 3
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Stuttgart']: 5,
    cities['Manchester']: 7,
    cities['Madrid']: 4,
    cities['Vienna']: 2
}

# Allowed direct flights (from, to)
allowed_flights = [
    (3, 0), (0, 3),  # Vienna <-> Stuttgart
    (1, 3), (3, 1),  # Manchester <-> Vienna
    (2, 3), (3, 2),  # Madrid <-> Vienna
    (1, 0), (0, 1),  # Manchester <-> Stuttgart
    (1, 2), (2, 1)   # Manchester <-> Madrid
]

# Create solver
s = Solver()

# Day variables: 1 to 15 (indices 0-14)
days = [Int(f'day_{i}') for i in range(15)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Manchester (days 1-7, indices 0-6)
for i in range(7):
    s.add(days[i] == cities['Manchester'])

# Fixed days in Stuttgart (days 11-15, indices 10-14)
for i in range(10, 15):
    s.add(days[i] == cities['Stuttgart'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 15):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(15):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")