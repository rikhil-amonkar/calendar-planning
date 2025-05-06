from z3 import *

# Define cities and their required days
cities = {
    0: 'Valencia',
    1: 'Athens',
    2: 'Naples',
    3: 'Zurich'
}

required_days = {
    0: 6,
    1: 6,
    2: 5,
    3: 6
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 2),  # Valencia → Naples
    (0, 1),  # Valencia → Athens
    (1, 2),  # Athens → Naples
    (2, 3),  # Naples → Zurich
    (1, 3),  # Athens → Zurich
    (3, 0),  # Zurich → Valencia
    (2, 0),  # Naples → Valencia
    (3, 1),  # Zurich → Athens
    (2, 1),  # Naples → Athens
    (3, 2)   # Zurich → Naples
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
    solver.add(days[i] <= 3)

# Add specific day constraints
# Must be in Athens at least once between day 1 and day 6
solver.add(Or([days[i] == 1 for i in range(6)]))
# Must be in Naples at least once between day 16 and day 20
solver.add(Or([days[i] == 2 for i in range(16, 20)]))

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