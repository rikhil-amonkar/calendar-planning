from z3 import *

# Define cities and their required days
cities = {
    0: 'Stuttgart',
    1: 'Manchester',
    2: 'Madrid',
    3: 'Vienna'
}

required_days = {
    0: 5,
    1: 7,
    2: 4,
    3: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (3, 0),  # Vienna → Stuttgart
    (1, 3),  # Manchester → Vienna
    (2, 3),  # Madrid → Vienna
    (1, 0),  # Manchester → Stuttgart
    (1, 2)   # Manchester → Madrid
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(15)]

solver = Solver()

# Add domain constraints for each day
for i in range(15):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 3)

# Add specific day constraints
# Attend wedding in Manchester from day 1 to day 7
for i in range(7):
    solver.add(days[i] == 1)
# Attend workshop in Stuttgart from day 11 to day 15
for i in range(10, 15):
    solver.add(days[i] == 0)

# Add transition constraints
for i in range(14):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(15)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(15):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")