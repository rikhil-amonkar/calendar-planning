from z3 import *

# Define cities with indices
cities = {
    'Brussels': 0,
    'Split': 1,
    'Barcelona': 2
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Brussels']: 2,
    cities['Split']: 5,
    cities['Barcelona']: 7
}

# Allowed direct flights (from, to)
allowed_flights = [
    (0, 2), (2, 0),  # Brussels <-> Barcelona
    (2, 1), (1, 2)   # Barcelona <-> Split
]

# Create solver
s = Solver()

# Day variables: 1 to 12 (indices 0-11)
days = [Int(f'day_{i}') for i in range(12)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Brussels (days 1-2, indices 0-1)
s.add(days[0] == cities['Brussels'])
s.add(days[1] == cities['Brussels'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 12):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(12):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")