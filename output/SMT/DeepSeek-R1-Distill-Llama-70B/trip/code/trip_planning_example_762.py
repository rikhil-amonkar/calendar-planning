from z3 import *

# Define cities and their required days
cities = {
    0: 'Dublin',
    1: 'Madrid',
    2: 'Oslo',
    3: 'London',
    4: 'Vilnius',
    5: 'Berlin'
}

required_days = {
    0: 3,
    1: 2,
    2: 3,
    3: 2,
    4: 3,
    5: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (3, 1),  # London → Madrid
    (2, 4),  # Oslo → Vilnius
    (5, 4),  # Berlin → Vilnius
    (1, 2),  # Madrid → Oslo
    (1, 0),  # Madrid → Dublin
    (3, 2),  # London → Oslo
    (1, 5),  # Madrid → Berlin
    (5, 2),  # Berlin → Oslo
    (0, 2),  # Dublin → Oslo
    (3, 0),  # London → Dublin
    (3, 5),  # London → Berlin
    (5, 0)   # Berlin → Dublin
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
    solver.add(days[i] <= 5)

# Add specific day constraints
# Madrid between day 2 and day 3
solver.add(Or([days[i] == 1 for i in range(2, 4)]))
# Berlin between day 3 and day 7
solver.add(Or([days[i] == 5 for i in range(3, 8)]))
# Dublin between day 7 and day 9
solver.add(Or([days[i] == 0 for i in range(7, 10)]))

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