from z3 import *

# Define cities with indices
cities = {
    'Split': 0,
    'Vilnius': 1,
    'Santorini': 2,
    'Madrid': 3
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Split']: 5,
    cities['Vilnius']: 4,
    cities['Santorini']: 2,
    cities['Madrid']: 6
}

# Allowed flights (bidirectional)
allowed_flights = [
    (0, 1), (1, 0),   # Split <-> Vilnius
    (0, 3), (3, 0),   # Split <-> Madrid
    (3, 2), (2, 3)    # Madrid <-> Santorini
]

# Create solver
s = Solver()

# Day variables: 1 to 14 (indices 0-13)
days = [Int(f'day_{i}') for i in range(14)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed constraints: Santorini on days 13-14 (indices 12-13)
s.add(days[12] == cities['Santorini'])
s.add(days[13] == cities['Santorini'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 14):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(14):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")