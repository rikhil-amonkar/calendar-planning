from z3 import *

# Define cities with indices
cities = {
    'Brussels': 0,
    'Helsinki': 1,
    'Split': 2,
    'Dubrovnik': 3,
    'Istanbul': 4,
    'Milan': 5,
    'Vilnius': 6,
    'Frankfurt': 7
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Brussels']: 3,
    cities['Helsinki']: 3,
    cities['Split']: 4,
    cities['Dubrovnik']: 2,
    cities['Istanbul']: 5,
    cities['Milan']: 4,
    cities['Vilnius']: 5,
    cities['Frankfurt']: 3
}

# Allowed direct flights (from, to)
allowed_flights = [
    (5, 7), (7, 5),   # Milan <-> Frankfurt
    (2, 7), (7, 2),   # Split <-> Frankfurt
    (5, 2), (2, 5),   # Milan <-> Split
    (0, 6), (6, 0),   # Brussels <-> Vilnius
    (0, 1), (1, 0),   # Brussels <-> Helsinki
    (4, 0), (0, 4),   # Istanbul <-> Brussels
    (5, 6), (6, 5),   # Milan <-> Vilnius
    (0, 5), (5, 0),   # Brussels <-> Milan
    (4, 1), (1, 4),   # Istanbul <-> Helsinki
    (1, 6), (6, 1),   # Helsinki <-> Vilnius
    (1, 3), (3, 1),   # Helsinki <-> Dubrovnik
    (2, 6), (6, 2),   # Split <-> Vilnius
    (3, 4),            # Dubrovnik -> Istanbul
    (4, 5), (5, 4),   # Istanbul <-> Milan
    (1, 7), (7, 1),   # Helsinki <-> Frankfurt
    (4, 6), (6, 4),   # Istanbul <-> Vilnius
    (2, 1), (1, 2),   # Split <-> Helsinki
    (5, 1), (1, 5),   # Milan <-> Helsinki
    (4, 7), (7, 4),   # Istanbul <-> Frankfurt
    (0, 7),            # Brussels -> Frankfurt
    (3, 7), (7, 3),   # Dubrovnik <-> Frankfurt
    (7, 6), (6, 7)    # Frankfurt <-> Vilnius
]

# Create solver
s = Solver()

# Day variables: 1 to 22 (indices 0-21)
days = [Int(f'day_{i}') for i in range(22)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Istanbul (days 1-5, indices 0-4)
for i in range(5):
    s.add(days[i] == cities['Istanbul'])

# Fixed days in Vilnius (days 18-22, indices 17-21)
for i in range(17, 22):
    s.add(days[i] == cities['Vilnius'])

# Fixed days in Frankfurt (days 16-18, indices 15-17)
for i in range(15, 18):
    s.add(days[i] == cities['Frankfurt'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 22):
    current = days[i]
    prev = days[i-1]
    valid_transitions = [And(prev == f, current == t) for (f, t) in allowed_flights]
    s.add(Or(current == prev, Or(valid_transitions)))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(22):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")