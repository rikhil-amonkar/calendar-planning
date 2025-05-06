from z3 import *

# Define cities with indices
cities = {
    'Zurich': 0,
    'Bucharest': 1,
    'Hamburg': 2,
    'Barcelona': 3,
    'Reykjavik': 4,
    'Stuttgart': 5,
    'Stockholm': 6,
    'Tallinn': 7,
    'Milan': 8,
    'London': 9
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Zurich']: 2,
    cities['Bucharest']: 2,
    cities['Hamburg']: 5,
    cities['Barcelona']: 4,
    cities['Reykjavik']: 5,
    cities['Stuttgart']: 5,
    cities['Stockholm']: 2,
    cities['Tallinn']: 4,
    cities['Milan']: 5,
    cities['London']: 3
}

# Allowed direct flights (from, to)
allowed_flights = [
    (9, 2), (2, 9),    # London <-> Hamburg
    (9, 4), (4, 9),    # London <-> Reykjavik
    (8, 3), (3, 8),    # Milan <-> Barcelona
    (4, 3), (3, 4),    # Reykjavik <-> Barcelona
    (4, 5),            # Reykjavik -> Stuttgart
    (6, 4), (4, 6),    # Stockholm <-> Reykjavik
    (9, 5), (5, 9),    # London <-> Stuttgart
    (8, 0), (0, 8),    # Milan <-> Zurich
    (9, 3), (3, 9),    # London <-> Barcelona
    (6, 2), (2, 6),    # Stockholm <-> Hamburg
    (0, 3), (3, 0),    # Zurich <-> Barcelona
    (6, 5), (5, 6),    # Stockholm <-> Stuttgart
    (8, 2), (2, 8),    # Milan <-> Hamburg
    (6, 7), (7, 6),    # Stockholm <-> Tallinn
    (2, 1), (1, 2),    # Hamburg <-> Bucharest
    (9, 1), (1, 9),    # London <-> Bucharest
    (8, 6), (6, 8),    # Milan <-> Stockholm
    (5, 2), (2, 5),    # Stuttgart <-> Hamburg
    (9, 0), (0, 9),    # London <-> Zurich
    (8, 4), (4, 8),    # Milan <-> Reykjavik
    (9, 6), (6, 9),    # London <-> Stockholm
    (8, 5), (5, 8),    # Milan <-> Stuttgart
    (6, 3), (3, 6),    # Stockholm <-> Barcelona
    (9, 8), (8, 9),    # London <-> Milan
    (0, 2), (2, 0),    # Zurich <-> Hamburg
    (1, 3), (3, 1),    # Bucharest <-> Barcelona
    (0, 6), (6, 0),    # Zurich <-> Stockholm
    (3, 7), (7, 3),    # Barcelona <-> Tallinn
    (0, 7), (7, 0),    # Zurich <-> Tallinn
    (2, 3), (3, 2),    # Hamburg <-> Barcelona
    (5, 3), (3, 5),    # Stuttgart <-> Barcelona
    (0, 4), (4, 0),    # Zurich <-> Reykjavik
    (0, 1), (1, 0)     # Zurich <-> Bucharest
]

# Create solver
s = Solver()

# Day variables: 1 to 28 (indices 0-27)
days = [Int(f'day_{i}') for i in range(28)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in London (days 1-3, indices 0-2)
for i in range(0, 3):
    s.add(days[i] == cities['London'])

# Fixed days in Milan (days 3-7, indices 2-6)
for i in range(2, 7):
    s.add(days[i] == cities['Milan'])

# Fixed days in Zurich (days 7-8, indices 6-7)
s.add(days[6] == cities['Zurich'])
s.add(days[7] == cities['Zurich'])

# Fixed days in Reykjavik (days 9-13, indices 8-12)
for i in range(8, 13):
    s.add(days[i] == cities['Reykjavik'])

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 28):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights])))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = [m[d] for d in days]
    # Print the schedule
    for i in range(28):
        day = i + 1
        city = inv_cities[schedule[i].as_long()]
        print(f"Day {day}: {city}")
else:
    print("No valid trip plan found.")