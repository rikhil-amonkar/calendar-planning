from z3 import *

# Define cities and their required days
cities = {
    0: 'Stockholm',
    1: 'Hamburg',
    2: 'Florence',
    3: 'Istanbul',
    4: 'Oslo',
    5: 'Vilnius',
    6: 'Santorini',
    7: 'Munich',
    8: 'Frankfurt',
    9: 'Krakow'
}

required_days = {
    0: 3,
    1: 5,
    2: 2,
    3: 5,
    4: 5,
    5: 5,
    6: 2,
    7: 5,
    8: 4,
    9: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (4, 0),  # Oslo → Stockholm
    (9, 8),  # Krakow → Frankfurt
    (9, 3),  # Krakow → Istanbul
    (7, 0),  # Munich → Stockholm
    (1, 0),  # Hamburg → Stockholm
    (9, 5),  # Krakow → Vilnius
    (4, 3),  # Oslo → Istanbul
    (3, 0),  # Istanbul → Stockholm
    (4, 9),  # Oslo → Krakow
    (5, 3),  # Vilnius → Istanbul
    (4, 5),  # Oslo → Vilnius
    (8, 3),  # Frankfurt → Istanbul
    (4, 8),  # Oslo → Frankfurt
    (7, 1),  # Munich → Hamburg
    (7, 3),  # Munich → Istanbul
    (4, 7),  # Oslo → Munich
    (8, 2),  # Frankfurt → Florence
    (4, 1),  # Oslo → Hamburg
    (5, 8),  # Vilnius → Frankfurt
    (2, 7),  # Florence → Munich
    (9, 7),  # Krakow → Munich
    (1, 3),  # Hamburg → Istanbul
    (8, 0),  # Frankfurt → Stockholm
    (0, 6),  # Stockholm → Santorini
    (8, 7),  # Frankfurt → Munich
    (6, 4),  # Santorini → Oslo
    (9, 0),  # Krakow → Stockholm
    (5, 7),  # Vilnius → Munich
    (8, 1)   # Frankfurt → Hamburg
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(32)]

solver = Solver()

# Add domain constraints for each day
for i in range(32):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 9)

# Add specific day constraints
# Attend workshop in Krakow between day 5 and day 9
for i in range(4, 9):
    solver.add(days[i] == 9)
# Annual show in Istanbul from day 25 to day 29
for i in range(24, 29):
    solver.add(days[i] == 3)

# Add transition constraints
for i in range(31):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(32)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(32):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")