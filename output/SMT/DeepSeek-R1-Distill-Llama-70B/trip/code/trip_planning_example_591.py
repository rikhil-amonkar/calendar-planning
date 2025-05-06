from z3 import *

# Define cities and their required days
cities = {
    0: 'Geneva',
    1: 'Munich',
    2: 'Valencia',
    3: 'Bucharest',
    4: 'Stuttgart'
}

required_days = {
    0: 4,
    1: 7,
    2: 6,
    3: 2,
    4: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 1),  # Geneva → Munich
    (1, 2),  # Munich → Valencia
    (2, 3),  # Valencia → Bucharest
    (3, 1),  # Bucharest → Munich
    (1, 3),  # Munich → Bucharest
    (2, 4),  # Valencia → Stuttgart
    (0, 2)   # Geneva → Valencia
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(17)]

solver = Solver()

# Add domain constraints for each day
for i in range(17):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 4)

# Add specific day constraints
# Visit relatives in Geneva between day 1 and day 4
for i in range(4):
    solver.add(days[i] == 0)
# Meet friends in Munich between day 4 and day 10
for i in range(3, 10):
    solver.add(days[i] == 1)

# Add transition constraints
for i in range(16):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(17)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(17):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")