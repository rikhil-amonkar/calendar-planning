from z3 import *

# Define cities and their required days
cities = {
    0: 'Paris',
    1: 'Madrid',
    2: 'Bucharest',
    3: 'Seville'
}

required_days = {
    0: 6,
    1: 7,
    2: 2,
    3: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 2),  # Paris → Bucharest
    (3, 0),  # Seville → Paris
    (1, 2),  # Madrid → Bucharest
    (1, 0),  # Madrid → Paris
    (1, 3)   # Madrid → Seville
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
# Annual show in Madrid between day 1 and day 7
for i in range(7):
    solver.add(days[i] == 1)
# Visit relatives in Bucharest on day 14 and day 15
solver.add(days[13] == 2)
solver.add(days[14] == 2)

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