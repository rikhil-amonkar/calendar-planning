from z3 import *

# Define cities and their required days
cities = {
    0: 'Istanbul',
    1: 'Rome',
    2: 'Seville',
    3: 'Naples',
    4: 'Santorini'
}

required_days = {
    0: 2,
    1: 3,
    2: 4,
    3: 7,
    4: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (1, 4),  # Rome → Santorini
    (2, 1),  # Seville → Rome
    (0, 3),  # Istanbul → Naples
    (3, 4),  # Naples → Santorini
    (1, 3),  # Rome → Naples
    (1, 0)   # Rome → Istanbul
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(16)]

solver = Solver()

# Add domain constraints for each day
for i in range(16):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 4)

# Add specific day constraints
# Visit relatives in Istanbul between day 6 and day 7
solver.add(days[5] == 0)
solver.add(days[6] == 0)
# Attend wedding in Santorini between day 13 and day 16
for i in range(12, 16):
    solver.add(days[i] == 4)

# Add transition constraints
for i in range(15):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(16)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(16):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")