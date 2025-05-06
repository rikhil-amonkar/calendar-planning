from z3 import *

# Define cities and their required days
cities = {
    0: 'Paris',
    1: 'Oslo',
    2: 'Porto',
    3: 'Geneva',
    4: 'Reykjavik'
}

required_days = {
    0: 6,
    1: 5,
    2: 7,
    3: 7,
    4: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 1),  # Paris → Oslo
    (3, 1),  # Geneva → Oslo
    (2, 0),  # Porto → Paris
    (3, 0),  # Geneva → Paris
    (3, 2),  # Geneva → Porto
    (0, 4),  # Paris → Reykjavik
    (4, 1),  # Reykjavik → Oslo
    (2, 1)   # Porto → Oslo
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(23)]

solver = Solver()

# Add domain constraints for each day
for i in range(23):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 4)

# Add specific day constraints
# Conference in Geneva on day 1 and day 7
solver.add(days[0] == 3)
solver.add(days[6] == 3)
# Visit relatives in Oslo between day 19 and day 23
for i in range(18, 23):
    solver.add(days[i] == 1)

# Add transition constraints
for i in range(22):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(23)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(23):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")