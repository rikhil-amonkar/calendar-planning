from z3 import *

# Define cities with indices
cities = {
    'Split': 0,
    'Santorini': 1,
    'London': 2
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Split']: 6,
    cities['Santorini']: 7,
    cities['London']: 7
}

# Allowed direct flights (from, to)
allowed_flights = [
    (2, 1), (1, 2),  # London <-> Santorini
    (0, 2), (2, 0)   # Split <-> London
]

# Create solver
s = Solver()

# Day variables: 1 to 18 (indices 0-17)
days = [Int(f'day_{i}') for i in range(18)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Santorini (days 12-18, indices 11-17)
for i in range(11, 18):
    s.add(days[i] == cities['Santorini'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 18):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(18):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")