from z3 import *

# Define cities with indices
cities = {
    'Prague': 0,
    'Berlin': 1,
    'Tallinn': 2,
    'Stockholm': 3
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Prague']: 2,
    cities['Berlin']: 3,
    cities['Tallinn']: 5,
    cities['Stockholm']: 5
}

# Allowed direct flights (from, to)
allowed_flights = [
    (1, 2), (2, 1),   # Berlin <-> Tallinn
    (0, 2), (2, 0),   # Prague <-> Tallinn
    (3, 2), (2, 3),   # Stockholm <-> Tallinn
    (0, 3), (3, 0),   # Prague <-> Stockholm
    (3, 1), (1, 3)    # Stockholm <-> Berlin
]

# Create solver
s = Solver()

# Day variables: 1 to 12 (indices 0-11)
days = [Int(f'day_{i}') for i in range(12)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Berlin (days 6 and 8, indices 5 and 7)
s.add(days[5] == cities['Berlin'])
s.add(days[7] == cities['Berlin'])

# Fixed days in Tallinn (days 8-12, indices 7-11)
for i in range(7, 12):
    s.add(days[i] == cities['Tallinn'])

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