from z3 import *

# Define cities and their required days
cities = {
    0: 'Oslo',
    1: 'Stuttgart',
    2: 'Venice',
    3: 'Split',
    4: 'Barcelona',
    5: 'Brussels',
    6: 'Copenhagen'
}

required_days = {
    0: 2,
    1: 3,
    2: 4,
    3: 4,
    4: 3,
    5: 3,
    6: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 1),  # Venice → Stuttgart
    (0, 5),  # Oslo → Brussels
    (3, 6),  # Split → Copenhagen
    (4, 6),  # Barcelona → Copenhagen
    (4, 2),  # Barcelona → Venice
    (5, 2),  # Brussels → Venice
    (4, 1),  # Barcelona → Stuttgart
    (6, 5),  # Copenhagen → Brussels
    (0, 3),  # Oslo → Split
    (0, 2),  # Oslo → Venice
    (4, 3),  # Barcelona → Split
    (0, 6),  # Oslo → Copenhagen
    (4, 0),  # Barcelona → Oslo
    (6, 1),  # Copenhagen → Stuttgart
    (3, 1),  # Split → Stuttgart
    (6, 2),  # Copenhagen → Venice
    (4, 5)   # Barcelona → Brussels
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(16)]

solver = Solver()

# Add domain constraints for each day
for i in range(16):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 6)

# Add specific day constraints
# Annual show in Barcelona between day 1 and day 3
solver.add(Or([days[i] == 4 for i in range(3)]))
# Meet friends in Oslo between day 3 and day 4
solver.add(Or([days[i] == 0 for i in [2, 3]]))
# Meet a friend in Brussels between day 9 and day 11
solver.add(Or([days[i] == 5 for i in range(8, 11)]))

# Add transition constraints
for i in range(15):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(16)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(16):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")