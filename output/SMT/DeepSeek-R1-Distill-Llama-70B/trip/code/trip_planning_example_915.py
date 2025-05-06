from z3 import *

# Define cities and their required days
cities = {
    0: 'Bucharest',
    1: 'Venice',
    2: 'Prague',
    3: 'Frankfurt',
    4: 'Zurich',
    5: 'Florence',
    6: 'Tallinn'
}

required_days = {
    0: 3,
    1: 5,
    2: 4,
    3: 5,
    4: 5,
    5: 5,
    6: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 6),  # Prague → Tallinn
    (2, 4),  # Prague → Zurich
    (5, 2),  # Florence → Prague
    (3, 0),  # Frankfurt → Bucharest
    (3, 1),  # Frankfurt → Venice
    (2, 0),  # Prague → Bucharest
    (0, 4),  # Bucharest → Zurich
    (6, 3),  # Tallinn → Frankfurt
    (4, 5),  # Zurich → Florence
    (3, 4),  # Frankfurt → Zurich
    (4, 1),  # Zurich → Venice
    (5, 3),  # Florence → Frankfurt
    (2, 3),  # Prague → Frankfurt
    (6, 4)   # Tallinn → Zurich
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(26)]

solver = Solver()

# Add domain constraints for each day
for i in range(26):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 6)

# Add specific day constraints
# Stay in Bucharest from day 1 to day 3
for i in range(3):
    solver.add(days[i] == 0)
# Attend wedding in Venice from day 22 to day 26
for i in range(21, 26):
    solver.add(days[i] == 1)
# Attend annual show in Frankfurt from day 12 to day 16
for i in range(11, 16):
    solver.add(days[i] == 3)
# Meet friends in Tallinn from day 8 to day 12
for i in range(7, 12):
    solver.add(days[i] == 6)

# Add transition constraints
for i in range(25):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(26)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(26):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")