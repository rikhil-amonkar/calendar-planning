from z3 import *

# Define cities and their required days
cities = {
    0: 'Oslo',
    1: 'Reykjavik',
    2: 'Stockholm',
    3: 'Munich',
    4: 'Frankfurt',
    5: 'Barcelona',
    6: 'Bucharest',
    7: 'Split'
}

required_days = {
    0: 2,
    1: 5,
    2: 4,
    3: 4,
    4: 4,
    5: 3,
    6: 2,
    7: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (1, 3), (3, 4), (7, 0), (1, 0), (6, 3), (0, 4), (6, 5), (5, 4),
    (1, 4), (5, 2), (5, 1), (2, 1), (5, 7), (6, 0), (6, 4), (7, 2),
    (5, 0), (2, 3), (2, 0), (7, 4), (5, 3), (2, 4), (7, 3)
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(20)]

solver = Solver()

# Add domain constraints for each day
for i in range(20):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 7)

# Add specific day constraints
# Oslo on days 16 and 17
solver.add(days[15] == 0)
solver.add(days[16] == 0)

# Reykjavik between days 9 and 13
solver.add(Or([days[i] == 1 for i in range(8, 13)]))

# Munich between days 13 and 16
solver.add(Or([days[i] == 3 for i in range(12, 16)]))

# Frankfurt between days 17 and 20
solver.add(Or([days[i] == 4 for i in range(16, 20)]))

# Add transition constraints
for i in range(19):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(20)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(20):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")