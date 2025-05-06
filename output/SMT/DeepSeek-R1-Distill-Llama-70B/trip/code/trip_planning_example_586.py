from z3 import *

# Define cities and their required days
cities = {
    0: 'Prague',
    1: 'Frankfurt',
    2: 'Naples',
    3: 'Helsinki',
    4: 'Lyon'
}

required_days = {
    0: 2,
    1: 3,
    2: 4,
    3: 4,
    4: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 4),  # Prague → Lyon
    (0, 1),  # Prague → Frankfurt
    (1, 4),  # Frankfurt → Lyon
    (3, 2),  # Helsinki → Naples
    (3, 1),  # Helsinki → Frankfurt
    (2, 1),  # Naples → Frankfurt
    (0, 3)   # Prague → Helsinki
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(12)]

solver = Solver()

# Add domain constraints for each day
for i in range(12):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 4)

# Add specific day constraints
# Attend workshop in Prague on day 1 and day 2
solver.add(days[0] == 0)
solver.add(days[1] == 0)
# Annual show in Helsinki between day 2 and day 5
for i in range(1, 5):
    solver.add(days[i] == 3)

# Add transition constraints
for i in range(11):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(12)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(12):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")