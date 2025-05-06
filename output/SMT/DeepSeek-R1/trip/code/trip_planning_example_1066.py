from z3 import *

# Define cities with indices
cities = {
    'Brussels': 0,
    'Bucharest': 1,
    'Stuttgart': 2,
    'Mykonos': 3,
    'Madrid': 4,
    'Helsinki': 5,
    'Split': 6,
    'London': 7
}

# Inverse mapping for output
inv_cities = {v: k for k, v in cities.items()}

# Required days per city
required_days = {
    cities['Brussels']: 4,
    cities['Bucharest']: 3,
    cities['Stuttgart']: 4,
    cities['Mykonos']: 2,
    cities['Madrid']: 2,
    cities['Helsinki']: 5,
    cities['Split']: 3,
    cities['London']: 5
}

# Allowed direct flights (from, to)
allowed_flights = [
    (5, 7), (7, 5),   # Helsinki <-> London
    (6, 4), (4, 6),   # Split <-> Madrid
    (5, 4), (4, 5),   # Helsinki <-> Madrid
    (7, 4), (4, 7),   # London <-> Madrid
    (0, 7), (7, 0),   # Brussels <-> London
    (1, 7), (7, 1),   # Bucharest <-> London
    (0, 1), (1, 0),   # Brussels <-> Bucharest
    (1, 4), (4, 1),   # Bucharest <-> Madrid
    (6, 5), (5, 6),   # Split <-> Helsinki
    (3, 4), (4, 3),   # Mykonos <-> Madrid
    (2, 7), (7, 2),   # Stuttgart <-> London
    (5, 0), (0, 5),   # Helsinki <-> Brussels
    (0, 4), (4, 0),   # Brussels <-> Madrid
    (6, 7), (7, 6),   # Split <-> London
    (2, 6), (6, 2),   # Stuttgart <-> Split
    (7, 3), (3, 7)    # London <-> Mykonos
]

# Create solver
s = Solver()

# Day variables: 1 to 21 (indices 0-20)
days = [Int(f'day_{i}') for i in range(21)]

# Constraints for each day to be a valid city
for d in days:
    s.add(Or([d == c for c in cities.values()]))

# Fixed days in Madrid (days 20-21, indices 19-20)
s.add(days[19] == cities['Madrid'])
s.add(days[20] == cities['Madrid'])

# Stuttgart must be visited at least 1 day between day 1-4 (indices 0-3)
stuttgart_in_period = [days[i] == cities['Stuttgart'] for i in range(4)]
s.add(Sum([If(cond, 1, 0) for cond in stuttgart_in_period]) >= 1)

# Count constraints for each city
for city, total in required_days.items():
    count = Sum([If(d == city, 1, 0) for d in days])
    s.add(count == total)

# Flight constraints between consecutive days
for i in range(1, 21):
    current = days[i]
    prev = days[i-1]
    s.add(Or(current == prev, Or([And(prev == f, current == t) for (f, t) in allowed_flights]))

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