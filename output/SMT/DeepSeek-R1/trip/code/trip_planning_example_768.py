from z3 import *

# Define cities with indices
cities = {
    'Mykonos': 0,
    'Nice': 1,
    'London': 2,
    'Copenhagen': 3,
    'Oslo': 4,
    'Tallinn': 5
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Mykonos']: 4,
    cities['Nice']: 3,
    cities['London']: 2,
    cities['Copenhagen']: 3,
    cities['Oslo']: 5,
    cities['Tallinn']: 4
}

# Allowed direct flights (bidirectional unless specified)
allowed_flights = [
    (2, 3), (3, 2),   # London <-> Copenhagen
    (3, 5), (5, 3),   # Copenhagen <-> Tallinn
    (5, 4), (4, 5),   # Tallinn <-> Oslo
    (0, 2), (2, 0),   # Mykonos <-> London
    (4, 1), (1, 4),   # Oslo <-> Nice
    (2, 1), (1, 2),   # London <-> Nice
    (0, 1), (1, 0),   # Mykonos <-> Nice
    (2, 4), (4, 2),   # London <-> Oslo
    (3, 1), (1, 3),   # Copenhagen <-> Nice
    (3, 4), (4, 3)    # Copenhagen <-> Oslo
]

# Create solver
s = Solver()

# Day variables: 1 to 16 (indices 0-15)
days = [Int(f'day_{i}') for i in range(16)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Nice (days 14-16, indices 13-15)
for i in range(13, 16):
    s.add(days[i] == cities['Nice'])

# Oslo must have at least 1 day between day 10-14 (indices 9-13)
s.add(Sum([If(days[i] == cities['Oslo'], 1, 0) for i in range(9, 14)]) >= 1)

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 16):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

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