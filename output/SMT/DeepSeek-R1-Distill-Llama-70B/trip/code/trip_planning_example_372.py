from z3 import *

# Define cities and their required days
cities = {
    0: 'Seville',
    1: 'Stuttgart',
    2: 'Porto',
    3: 'Madrid'
}

required_days = {
    0: 2,
    1: 7,
    2: 3,
    3: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 1),  # Porto → Stuttgart
    (0, 2),  # Seville → Porto
    (3, 2),  # Madrid → Porto
    (3, 0)   # Madrid → Seville
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(13)]

solver = Solver()

# Add domain constraints for each day
for i in range(13):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 3)

# Add specific day constraints
# Visit relatives in Madrid between day 1 and day 4
for i in range(4):
    solver.add(days[i] == 3)
# Attend conference in Stuttgart on day 7 and day 13
solver.add(days[6] == 1)
solver.add(days[12] == 1)

# Add transition constraints
for i in range(12):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(13)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(13):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")