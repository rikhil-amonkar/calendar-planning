from z3 import *

# Define cities with indices
cities = {
    'Mykonos': 0,
    'Budapest': 1,
    'Hamburg': 2
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Mykonos']: 6,
    cities['Budapest']: 3,
    cities['Hamburg']: 2
}

# Allowed direct flights (from, to)
allowed_flights = [
    (0, 1), (1, 0),  # Mykonos <-> Budapest
    (1, 2), (2, 1)   # Budapest <-> Hamburg
]

# Create solver
s = Solver()

# Day variables: 1 to 9 (indices 0-8)
days = [Int(f'day_{i}') for i in range(9)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed conference days in Mykonos (day4 and day9, indices 3 and 8)
s.add(days[3] == cities['Mykonos'])
s.add(days[8] == cities['Mykonos'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 9):
    current = days[i]
    prev = days[i-1]
    # Allow staying in the same city or direct flight
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(9):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")