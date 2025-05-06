from z3 import *

# Define cities and their required days
cities = {
    0: 'Vienna',
    1: 'Lyon',
    2: 'Edinburgh',
    3: 'Reykjavik',
    4: 'Stuttgart',
    5: 'Manchester',
    6: 'Split',
    7: 'Prague'
}

required_days = {
    0: 4,
    1: 3,
    2: 4,
    3: 5,
    4: 5,
    5: 2,
    6: 5,
    7: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (3, 4),  # Reykjavik → Stuttgart
    (4, 6),  # Stuttgart → Split
    (4, 0),  # Stuttgart → Vienna
    (7, 5),  # Prague → Manchester
    (2, 7),  # Edinburgh → Prague
    (5, 6),  # Manchester → Split
    (7, 0),  # Prague → Vienna
    (0, 5),  # Vienna → Manchester
    (7, 6),  # Prague → Split
    (0, 1),  # Vienna → Lyon
    (4, 2),  # Stuttgart → Edinburgh
    (6, 1),  # Split → Lyon
    (4, 5),  # Stuttgart → Manchester
    (7, 1),  # Prague → Lyon
    (3, 0),  # Reykjavik → Vienna
    (7, 3),  # Prague → Reykjavik
    (0, 6)   # Vienna → Split
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
# Edinburgh between day 5 and day 8
for i in range(4, 8):
    solver.add(Or(days[i] == 2))
solver.add(Or(days[4] == 2, days[5] == 2, days[6] == 2, days[7] == 2))

# Split between day 19 and day 23
for i in range(18, 23):
    solver.add(Or(days[i] == 6))
solver.add(Or(days[18] == 6, days[19] == 6, days[20] == 6, days[21] == 6, days[22] == 6))

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