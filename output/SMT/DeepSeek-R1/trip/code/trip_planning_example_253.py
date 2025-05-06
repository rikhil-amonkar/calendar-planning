from z3 import *

# Define cities with indices
cities = {
    'Amsterdam': 0,
    'Vienna': 1,
    'Santorini': 2,
    'Lyon': 3
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Amsterdam']: 3,
    cities['Vienna']: 7,
    cities['Santorini']: 4,
    cities['Lyon']: 3
}

# Allowed direct flights (bidirectional)
allowed_flights = [
    (1, 3), (3, 1),   # Vienna <-> Lyon
    (1, 2), (2, 1),   # Vienna <-> Santorini
    (1, 0), (0, 1),   # Vienna <-> Amsterdam
    (0, 2), (2, 0),   # Amsterdam <-> Santorini
    (3, 0), (0, 3)    # Lyon <-> Amsterdam
]

# Create solver
s = Solver()

# Day variables: 1 to 14 (indices 0-13)
days = [Int(f'day_{i}') for i in range(14)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Amsterdam (days 9-11, indices 8-10)
for i in range(8, 11):
    s.add(days[i] == cities['Amsterdam'])

# Fixed days in Lyon (days 7-9, indices 6-8)
for i in range(6, 9):
    s.add(days[i] == cities['Lyon'])

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