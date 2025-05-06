from z3 import *

# Define cities with indices
cities = {
    'Warsaw': 0,
    'Riga': 1,
    'Budapest': 2,
    'Paris': 3
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Riga']: 7,
    cities['Budapest']: 7,
    cities['Paris']: 4,
    cities['Warsaw']: 2
}

# Allowed direct flights (from, to)
allowed_flights = [
    (0, 2), (2, 0),  # Warsaw <-> Budapest
    (0, 1), (1, 0),  # Warsaw <-> Riga
    (2, 3), (3, 2),  # Budapest <-> Paris
    (0, 3), (3, 0),  # Warsaw <-> Paris
    (3, 1), (1, 3)   # Paris <-> Riga
]

# Create solver
s = Solver()

# Day variables: 1 to 17 (indices 0-16)
days = [Int(f'day_{i}') for i in range(17)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Warsaw (days 1-2, indices 0-1)
s.add(days[0] == cities['Warsaw'])
s.add(days[1] == cities['Warsaw'])

# Fixed days in Riga (days 11-17, indices 10-16)
for i in range(10, 17):
    s.add(days[i] == cities['Riga'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 17):
    current = days[i]
    prev = days[i-1]
    # Allow staying in the same city or direct flight
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

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