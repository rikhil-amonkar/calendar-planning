from z3 import *

# Define cities with indices
cities = {
    'London': 0,
    'Santorini': 1,
    'Istanbul': 2
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['London']: 3,
    cities['Santorini']: 6,
    cities['Istanbul']: 3
}

# Allowed direct flights (bidirectional)
allowed_flights = [
    (2, 0), (0, 2),   # Istanbul <-> London
    (0, 1), (1, 0)    # London <-> Santorini
]

# Create solver
s = Solver()

# Day variables: 1 to 10 (indices 0-9)
days = [Int(f'day_{i}') for i in range(10)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Santorini (days 5-10, indices 4-9)
for i in range(4, 10):
    s.add(days[i] == cities['Santorini'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 10):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(10):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")