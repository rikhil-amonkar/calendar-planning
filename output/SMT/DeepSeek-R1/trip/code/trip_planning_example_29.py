from z3 import *

# Define cities with indices
cities = {
    'Krakow': 0,
    'Dubrovnik': 1,
    'Frankfurt': 2
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Krakow']: 2,
    cities['Dubrovnik']: 7,
    cities['Frankfurt']: 3
}

# Allowed direct flights (from, to)
allowed_flights = [
    (2, 0), (0, 2),  # Frankfurt <-> Krakow
    (1, 2), (2, 1)   # Dubrovnik <-> Frankfurt
]

# Create solver
s = Solver()

# Day variables: 1 to 10 (indices 0-9)
days = [Int(f'day_{i}') for i in range(10)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Krakow (days 9-10, indices 8-9)
s.add(days[8] == cities['Krakow'])
s.add(days[9] == cities['Krakow'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 10):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights]))

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