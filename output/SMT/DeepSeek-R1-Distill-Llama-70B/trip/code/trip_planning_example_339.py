from z3 import *

# Define cities and their required days
cities = {
    0: 'Riga',
    1: 'Budapest',
    2: 'Paris',
    3: 'Warsaw'
}

required_days = {
    0: 7,
    1: 7,
    2: 4,
    3: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (3, 1),  # Warsaw → Budapest
    (3, 0),  # Warsaw → Riga
    (1, 2),  # Budapest → Paris
    (3, 2),  # Warsaw → Paris
    (2, 0)   # Paris → Riga
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(17)]

solver = Solver()

# Add domain constraints for each day
for i in range(17):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 3)

# Add specific day constraints
# Annual show in Warsaw between day 1 and day 2
solver.add(days[0] == 3)
solver.add(days[1] == 3)
# Wedding in Riga between day 11 and day 17
for i in range(10, 17):
    solver.add(days[i] == 0)

# Add transition constraints
for i in range(16):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(17)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(17):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")