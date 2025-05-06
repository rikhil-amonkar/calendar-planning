from z3 import *

# Define cities with indices
cities = {
    'Venice': 0,
    'Mykonos': 1,
    'Vienna': 2
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Venice']: 6,
    cities['Mykonos']: 2,
    cities['Vienna']: 4
}

# Allowed direct flights (from, to)
allowed_flights = [
    (1, 2), (2, 1),  # Mykonos <-> Vienna
    (2, 0), (0, 2)   # Vienna <-> Venice
]

# Create solver
s = Solver()

# Day variables: 1 to 10 (index 0 is day1, index 9 is day10)
days = [Int(f'day_{i}') for i in range(10)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Venice from day5 to day10 (indices 4-9)
for i in range(4, 10):
    s.add(days[i] == cities['Venice'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 10):
    current = days[i]
    prev = days[i-1]
    # Allow staying in the same city or direct flight
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

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