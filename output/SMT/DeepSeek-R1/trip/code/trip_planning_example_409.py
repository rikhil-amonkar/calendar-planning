from z3 import *

# Define cities with indices
cities = {
    'Hamburg': 0,
    'Zurich': 1,
    'Helsinki': 2,
    'Bucharest': 3,
    'Split': 4
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Hamburg']: 2,
    cities['Zurich']: 3,
    cities['Helsinki']: 2,
    cities['Bucharest']: 2,
    cities['Split']: 7
}

# Allowed direct flights (from, to)
allowed_flights = [
    (1, 2), (2, 1),   # Zurich <-> Helsinki
    (0, 3), (3, 0),   # Hamburg <-> Bucharest
    (2, 0), (0, 2),   # Helsinki <-> Hamburg
    (1, 0), (0, 1),   # Zurich <-> Hamburg
    (1, 3), (3, 1),   # Zurich <-> Bucharest
    (1, 4), (4, 1),   # Zurich <-> Split
    (2, 4), (4, 2),   # Helsinki <-> Split
    (4, 0), (0, 4)    # Split <-> Hamburg
]

# Create solver
s = Solver()

# Day variables: 1 to 12 (indices 0-11)
days = [Int(f'day_{i}') for i in range(12)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Zurich (days 1-3, indices 0-2)
s.add(days[0] == cities['Zurich'])
s.add(days[1] == cities['Zurich'])
s.add(days[2] == cities['Zurich'])

# Fixed days in Split (days 4 and 10, indices 3 and 9)
s.add(days[3] == cities['Split'])
s.add(days[9] == cities['Split'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 12):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

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