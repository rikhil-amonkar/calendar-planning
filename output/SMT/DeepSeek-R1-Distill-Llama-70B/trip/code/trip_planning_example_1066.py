from z3 import *

# Define cities and their required days
cities = {
    0: 'Brussels',
    1: 'Bucharest',
    2: 'Stuttgart',
    3: 'Mykonos',
    4: 'Madrid',
    5: 'Helsinki',
    6: 'Split',
    7: 'London'
}

required_days = {
    0: 4,
    1: 3,
    2: 4,
    3: 2,
    4: 2,
    5: 5,
    6: 3,
    7: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (5, 7),  # Helsinki → London
    (6, 4),  # Split → Madrid
    (5, 4),  # Helsinki → Madrid
    (7, 4),  # London → Madrid
    (0, 7),  # Brussels → London
    (1, 7),  # Bucharest → London
    (0, 1),  # Brussels → Bucharest
    (1, 4),  # Bucharest → Madrid
    (6, 5),  # Split → Helsinki
    (3, 4),  # Mykonos → Madrid
    (2, 7),  # Stuttgart → London
    (5, 0),  # Helsinki → Brussels
    (0, 4),  # Brussels → Madrid
    (6, 7),  # Split → London
    (2, 6)   # Stuttgart → Split
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(21)]

solver = Solver()

# Add domain constraints for each day
for i in range(21):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 7)

# Add specific day constraints
# Meet a friend in Stuttgart between day 1 and day 4
for i in range(4):
    solver.add(days[i] == 2)
# Attend conference in Madrid on day 20 and day 21
solver.add(days[19] == 4)
solver.add(days[20] == 4)
# Attend annual show in Helsinki between day 7 and day 11
for i in range(6, 11):
    solver.add(days[i] == 5)

# Add transition constraints
for i in range(20):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(21)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(21):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")