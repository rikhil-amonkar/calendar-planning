from z3 import *

# Define cities with indices
cities = {
    'Lisbon': 0,
    'Dubrovnik': 1,
    'Copenhagen': 2,
    'Prague': 3,
    'Tallinn': 4,
    'Stockholm': 5,
    'Split': 6,
    'Lyon': 7
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Lisbon']: 2,
    cities['Dubrovnik']: 5,
    cities['Copenhagen']: 5,
    cities['Prague']: 3,
    cities['Tallinn']: 2,
    cities['Stockholm']: 4,
    cities['Split']: 3,
    cities['Lyon']: 2
}

# Allowed direct flights (bidirectional)
allowed_flights = [
    (1, 5), (5, 1),   # Dubrovnik <-> Stockholm
    (0, 2), (2, 0),   # Lisbon <-> Copenhagen
    (0, 7), (7, 0),   # Lisbon <-> Lyon
    (2, 5), (5, 2),   # Copenhagen <-> Stockholm
    (2, 6), (6, 2),   # Copenhagen <-> Split
    (3, 5), (5, 3),   # Prague <-> Stockholm
    (4, 5), (5, 4),   # Tallinn <-> Stockholm
    (3, 7), (7, 3),   # Prague <-> Lyon
    (0, 5), (5, 0),   # Lisbon <-> Stockholm
    (3, 0), (0, 3),   # Prague <-> Lisbon
    (5, 6), (6, 5),   # Stockholm <-> Split
    (3, 2), (2, 3),   # Prague <-> Copenhagen
    (6, 7), (7, 6),   # Split <-> Lyon
    (2, 1), (1, 2),   # Copenhagen <-> Dubrovnik
    (3, 6), (6, 3),   # Prague <-> Split
    (4, 2), (2, 4),   # Tallinn <-> Copenhagen
    (4, 3), (3, 4)    # Tallinn <-> Prague
]

# Create solver
s = Solver()

# Day variables: 1 to 19 (indices 0-18)
days = [Int(f'day_{i}') for i in range(19)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Tallinn (days 1-2, indices 0-1)
for i in range(0, 2):
    s.add(days[i] == cities['Tallinn'])

# Fixed days in Lisbon (days 4-5, indices 3-4)
for i in range(3, 5):
    s.add(days[i] == cities['Lisbon'])

# Fixed days in Stockholm (days 13-16, indices 12-15)
for i in range(12, 16):
    s.add(days[i] == cities['Stockholm'])

# Fixed days in Lyon (days 18-19, indices 17-18)
for i in range(17, 19):
    s.add(days[i] == cities['Lyon'])

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