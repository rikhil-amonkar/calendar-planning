from z3 import *

# Define cities with indices
cities = {
    'Reykjavik': 0,
    'Istanbul': 1,
    'Edinburgh': 2,
    'Oslo': 3,
    'Stuttgart': 4,
    'Bucharest': 5
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Reykjavik']: 5,
    cities['Istanbul']: 4,
    cities['Edinburgh']: 5,
    cities['Oslo']: 2,
    cities['Stuttgart']: 3,
    cities['Bucharest']: 5
}

# Allowed flights (bidirectional and unidirectional)
allowed_flights = [
    # Bidirectional
    (5, 3), (3, 5),   # Bucharest <-> Oslo
    (1, 3), (3, 1),   # Istanbul <-> Oslo
    (5, 1), (1, 5),   # Bucharest <-> Istanbul
    (4, 2), (2, 4),   # Stuttgart <-> Edinburgh
    (1, 2), (2, 1),   # Istanbul <-> Edinburgh
    (3, 0), (0, 3),   # Oslo <-> Reykjavik
    (1, 4), (4, 1),   # Istanbul <-> Stuttgart
    (3, 2), (2, 3),   # Oslo <-> Edinburgh
    # Unidirectional
    (0, 4)            # Reykjavik → Stuttgart
]

# Create solver
s = Solver()

# Day variables: 1 to 19 (indices 0-18)
days = [Int(f'day_{i}') for i in range(19)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed constraints
# Istanbul days 5-8 (indices 4-7)
for i in range(4, 8):
    s.add(days[i] == cities['Istanbul'])

# Oslo days 8-9 (indices 7-8)
s.add(days[7] == cities['Oslo'])
s.add(days[8] == cities['Oslo'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 19):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(19):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")