from z3 import *

# Define cities and their required days
cities = {
    0: 'Riga',
    1: 'Vilnius',
    2: 'Dublin'
}

required_days = {
    0: 5,
    1: 7,
    2: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 0),  # Dublin → Riga
    (0, 1)   # Riga → Vilnius
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
    solver.add(days[i] <= 2)

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