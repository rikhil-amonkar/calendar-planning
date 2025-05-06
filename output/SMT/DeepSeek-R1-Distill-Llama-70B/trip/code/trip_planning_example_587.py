from z3 import *

# Define cities and their required days
cities = {
    0: 'Manchester',
    1: 'Istanbul',
    2: 'Venice',
    3: 'Krakow',
    4: 'Lyon'
}

required_days = {
    0: 3,
    1: 7,
    2: 7,
    3: 6,
    4: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 2),  # Manchester → Venice
    (0, 1),  # Manchester → Istanbul
    (2, 1),  # Venice → Istanbul
    (1, 3),  # Istanbul → Krakow
    (2, 4),  # Venice → Lyon
    (4, 1),  # Lyon → Istanbul
    (0, 3)   # Manchester → Krakow
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
    solver.add(days[i] <= 4)

# Add specific day constraints
# Attend wedding in Manchester between day 1 and day 3
solver.add(Or([days[i] == 0 for i in range(3)]))
# Attend workshop in Venice between day 3 and day 9
solver.add(Or([days[i] == 2 for i in range(2, 9)]))

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