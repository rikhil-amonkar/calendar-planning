from z3 import *

# Define cities and their required days
cities = {
    0: 'Stuttgart',
    1: 'Istanbul',
    2: 'Vilnius',
    3: 'Seville',
    4: 'Geneva',
    5: 'Valencia',
    6: 'Munich',
    7: 'Reykjavik'
}

required_days = {
    0: 4,
    1: 4,
    2: 4,
    3: 3,
    4: 5,
    5: 5,
    6: 3,
    7: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (4, 1),  # Geneva → Istanbul
    (7, 6),  # Reykjavik → Munich
    (0, 5),  # Stuttgart → Valencia
    (7, 0),  # Reykjavik → Stuttgart
    (0, 1),  # Stuttgart → Istanbul
    (6, 4),  # Munich → Geneva
    (1, 2),  # Istanbul → Vilnius
    (5, 3),  # Valencia → Seville
    (5, 1),  # Valencia → Istanbul
    (2, 6),  # Vilnius → Munich
    (3, 6),  # Seville → Munich
    (6, 1),  # Munich → Istanbul
    (5, 4),  # Valencia → Geneva
    (5, 6),  # Valencia → Munich
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(25)]

solver = Solver()

# Add domain constraints for each day
for i in range(25):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 7)

# Add specific day constraints
# Attend conference in Stuttgart from day 4 to day 7
for i in range(3, 7):
    solver.add(days[i] == 0)
# Attend workshop in Reykjavik from day 1 to day 4
for i in range(3):
    solver.add(days[i] == 7)
# Annual show in Munich from day 13 to day 15
for i in range(12, 15):
    solver.add(days[i] == 6)

# Add transition constraints
for i in range(24):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(25)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(25):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")