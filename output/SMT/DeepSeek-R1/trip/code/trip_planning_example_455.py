from z3 import *

# Define cities with indices
cities = {
    'Reykjavik': 0,
    'Riga': 1,
    'Warsaw': 2,
    'Istanbul': 3,
    'Krakow': 4
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Reykjavik']: 7,
    cities['Riga']: 2,
    cities['Warsaw']: 3,
    cities['Istanbul']: 6,
    cities['Krakow']: 7
}

# Allowed direct flights (from, to)
allowed_flights = [
    (3, 4), (4, 3),   # Istanbul <-> Krakow
    (2, 0), (0, 2),   # Warsaw <-> Reykjavik
    (3, 2), (2, 3),   # Istanbul <-> Warsaw
    (1, 3), (3, 1),   # Riga <-> Istanbul
    (4, 2), (2, 4),   # Krakow <-> Warsaw
    (1, 2), (2, 1)    # Riga <-> Warsaw
]

# Create solver
s = Solver()

# Day variables: 1 to 21 (indices 0-20)
days = [Int(f'day_{i}') for i in range(21)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Riga (days 1-2, indices 0-1)
s.add(days[0] == cities['Riga'])
s.add(days[1] == cities['Riga'])

# Fixed days in Istanbul (days 2-7, indices 1-6)
for i in range(1, 7):
    s.add(days[i] == cities['Istanbul'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 21):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(21):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")