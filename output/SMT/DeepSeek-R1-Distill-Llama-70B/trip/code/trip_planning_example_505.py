from z3 import *

# Define cities and their required days
cities = {
    0: 'Prague',
    1: 'Stuttgart',
    2: 'Split',
    3: 'Krakow',
    4: 'Florence'
}

required_days = {
    0: 4,
    1: 2,
    2: 2,
    3: 2,
    4: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (1, 2),  # Stuttgart → Split
    (0, 4),  # Prague → Florence
    (3, 1),  # Krakow → Stuttgart
    (3, 2),  # Krakow → Split
    (2, 0),  # Split → Prague
    (3, 0)   # Krakow → Prague
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(8)]

solver = Solver()

# Add domain constraints for each day
for i in range(8):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 4)

# Add specific day constraints
# Wedding in Stuttgart on day 2 and day 3
solver.add(days[1] == 1)
solver.add(days[2] == 1)
# Meet friends in Split on day 3 and day 4
solver.add(days[2] == 2)
solver.add(days[3] == 2)

# Add transition constraints
for i in range(7):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(8)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(8):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")