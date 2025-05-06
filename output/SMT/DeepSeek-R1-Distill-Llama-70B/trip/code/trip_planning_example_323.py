from z3 import *

# Define cities and their required days
cities = {
    0: 'Split',
    1: 'Oslo',
    2: 'London',
    3: 'Porto'
}

required_days = {
    0: 5,
    1: 2,
    2: 7,
    3: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 1),  # London → Oslo
    (0, 1),  # Split → Oslo
    (1, 3),  # Oslo → Porto
    (2, 0)   # London → Split
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
    solver.add(days[i] <= 3)

# Add specific day constraints
# Annual show in Split from day 7 to day 11 (days 6 to 10)
for i in range(6, 11):
    solver.add(days[i] == 0)
# Visit relatives in London from day 1 to day 7 (days 0 to 6)
for i in range(7):
    solver.add(days[i] == 2)

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