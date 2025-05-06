from z3 import *

# Define cities and their required days
cities = {
    0: 'Stuttgart',
    1: 'Edinburgh',
    2: 'Athens',
    3: 'Split',
    4: 'Krakow',
    5: 'Venice',
    6: 'Mykonos'
}

required_days = {
    0: 3,
    1: 4,
    2: 4,
    3: 2,
    4: 4,
    5: 5,
    6: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (4, 3),  # Krakow → Split
    (3, 2),  # Split → Athens
    (1, 4),  # Edinburgh → Krakow
    (5, 0),  # Venice → Stuttgart
    (4, 0),  # Krakow → Stuttgart
    (1, 0),  # Edinburgh → Stuttgart
    (0, 2),  # Stuttgart → Athens
    (5, 1),  # Venice → Edinburgh
    (2, 6),  # Athens → Mykonos
    (5, 2),  # Venice → Athens
    (0, 3),  # Stuttgart → Split
    (1, 2),  # Edinburgh → Athens
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
    solver.add(days[i] <= 6)

# Add specific day constraints
# Workshop in Stuttgart between day 11 and day 13
for i in range(10, 13):
    solver.add(days[i] == 0)
# Meet friends in Split between day 13 and day 14
solver.add(days[12] == 3)
solver.add(days[13] == 3)
# Meet a friend in Krakow between day 8 and day 11
for i in range(7, 11):
    solver.add(days[i] == 4)

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