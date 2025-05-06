from z3 import *

# Define cities with indices
cities = {
    'Split': 0,
    'Oslo': 1,
    'London': 2,
    'Porto': 3
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Split']: 5,
    cities['Oslo']: 2,
    cities['London']: 7,
    cities['Porto']: 5
}

# Allowed direct flights (from, to)
allowed_flights = [
    (2, 1), (1, 2),  # London <-> Oslo
    (0, 1), (1, 0),  # Split <-> Oslo
    (1, 3), (3, 1),  # Oslo <-> Porto
    (2, 0), (0, 2)   # London <-> Split
]

# Create solver
s = Solver()

# Day variables: 1 to 16 (indices 0-15)
days = [Int(f'day_{i}') for i in range(16)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in London (days 1-7, indices 0-6)
for i in range(7):
    s.add(days[i] == cities['London'])

# Fixed days in Split (days 7-11, indices 6-10)
for i in range(6, 11):
    s.add(days[i] == cities['Split'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 16):
    current = days[i]
    prev = days[i-1]
    # Allow staying in the same city or direct flight
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