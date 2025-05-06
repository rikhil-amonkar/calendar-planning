from z3 import *

# Define cities and their required days
cities = {
    0: 'Hamburg',
    1: 'Munich',
    2: 'Manchester',
    3: 'Lyon',
    4: 'Split'
}

required_days = {
    0: 7,
    1: 6,
    2: 2,
    3: 2,
    4: 7
}

# Define allowed transitions between cities
allowed_transitions = [
    (4, 1),  # Split → Munich
    (1, 2),  # Munich → Manchester
    (0, 2),  # Hamburg → Manchester
    (0, 1),  # Hamburg → Munich
    (4, 3),  # Split → Lyon
    (3, 1),  # Lyon → Munich
    (0, 4),  # Hamburg → Split
    (2, 4)   # Manchester → Split
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
    solver.add(days[i] <= 4)

# Add specific day constraints
# Manchester on days 19 and 20
solver.add(days[18] == 2)
solver.add(days[19] == 2)

# Lyon on days 13 and 14
solver.add(days[12] == 3)
solver.add(days[13] == 3)

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